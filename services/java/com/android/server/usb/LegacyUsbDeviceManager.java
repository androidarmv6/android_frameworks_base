/*
 * Copyright (C) 2011 The Android Open Source Project
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions an
 * limitations under the License.
 */

package com.android.server.usb;

import android.app.Notification;
import android.app.NotificationManager;
import android.app.PendingIntent;
import android.content.BroadcastReceiver;
import android.content.ComponentName;
import android.content.ContentResolver;
import android.content.Context;
import android.content.Intent;
import android.content.IntentFilter;
import android.content.pm.PackageManager;
import android.content.res.Resources;
import android.database.ContentObserver;
import android.hardware.usb.UsbManager;
import android.os.Build;
import android.os.FileUtils;
import android.os.Handler;
import android.os.Looper;
import android.os.Message;
import android.os.ParcelFileDescriptor;
import android.os.SystemClock;
import android.os.SystemProperties;
import android.os.UEventObserver;
import android.os.UserHandle;
import android.os.storage.StorageManager;
import android.os.storage.StorageVolume;
import android.provider.Settings;
import android.util.Pair;
import android.util.Slog;

import com.android.internal.annotations.GuardedBy;
import com.android.server.FgThread;

import java.io.File;
import java.io.FileDescriptor;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.Arrays;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Scanner;

/**
 * LegacyUsbDeviceManager manages USB state in devices with legacy USB stacks.
 */
public class LegacyUsbDeviceManager extends UsbDeviceManager {

    private static final String TAG = LegacyUsbDeviceManager.class.getSimpleName();
    private static final boolean DEBUG = false;

    private static final String USB_CONNECTED_MATCH =
            "DEVPATH=/devices/virtual/switch/usb_connected";
    private static final String USB_CONFIGURATION_MATCH =
            "DEVPATH=/devices/virtual/switch/usb_configuration";
    private static final String USB_LEGACY_MATCH =
            "DEVPATH=/devices/virtual/switch/usb_mass_storage";
    private static final String USB_CONNECTED_PATH =
            "/sys/class/switch/usb_connected/state";
    private static final String USB_CONFIGURATION_PATH =
            "/sys/class/switch/usb_configuration/state";
    private static final String USB_LEGACY_PATH =
            "/sys/class/switch/usb_mass_storage/state";
    private static final String FUNCTIONS_PATH =
            "/sys/devices/virtual/usb_composite/";
    private static final String MASS_STORAGE_FILE_PATH =
            Resources.getSystem().getString(com.android.internal.R.string.config_legacyUmsLunFile);

    private static final int MSG_UPDATE_STATE = 0;
    private static final int MSG_ENABLE_ADB = 1;
    private static final int MSG_SET_CURRENT_FUNCTIONS = 2;
    private static final int MSG_SYSTEM_READY = 3;
    private static final int MSG_BOOT_COMPLETED = 4;
    private static final int MSG_USER_SWITCHED = 5;

    private boolean mConnected = false;
    private boolean mConfigured = false;

    // Delay for debouncing USB disconnects.
    // We often get rapid connect/disconnect events when enabling USB functions,
    // which need debouncing.
    private static final int UPDATE_DELAY = 1000;

    private static final String BOOT_MODE_PROPERTY = "ro.bootmode";

    private LegacyUsbHandler mHandler;
    private boolean mBootCompleted;

    private final Object mLock = new Object();

    private final Context mContext;
    private final ContentResolver mContentResolver;
    @GuardedBy("mLock")
    private UsbSettingsManager mCurrentSettings;
    private NotificationManager mNotificationManager;
    private boolean mUseUsbNotification;
    private boolean mAdbEnabled;
    private Map<String, List<Pair<String, String>>> mOemModeMap;
    private UsbDebuggingManager mDebuggingManager;
    private boolean mLegacy = false;

    private class AdbSettingsObserver extends ContentObserver {
        public AdbSettingsObserver() {
            super(null);
        }
        @Override
        public void onChange(boolean selfChange) {
            boolean enable = (Settings.Global.getInt(mContentResolver,
                    Settings.Global.ADB_ENABLED,
                    "eng".equals(Build.TYPE) ? 1 : 0) > 0);
            mHandler.sendMessage(MSG_ENABLE_ADB, enable);
        }
    }

    /*
     * Listens for uevent messages from the kernel to monitor the USB state
     */
    private final UEventObserver mUEventObserver = new UEventObserver() {
        @Override
        public void onUEvent(UEventObserver.UEvent event) {
            if (DEBUG) Slog.v(TAG, "USB UEVENT: " + event.toString());

            String name = event.get("SWITCH_NAME");
            String state = event.get("SWITCH_STATE");

            if (name != null && state != null) {
                if (mLegacy) {
                    if ("usb_mass_storage".equals(name)) {
                        mConnected  = "online".equals(state);
                        mConfigured = "online".equals(state);
                    }
                } else {
                    if ("usb_connected".equals(name))
                        mConnected = "1".equals(state);
                    else if ("usb_configuration".equals(name))
                        mConfigured = "1".equals(state);
                }

                if (!mConnected && !mConfigured) state = "DISCONNECTED";
                else if(mConnected && !mConfigured) state = "CONNECTED";
                else if(mConnected && mConfigured) state = "CONFIGURED";
                else state = "UNKNOWN";
            }

            if (state != null) {
                mHandler.updateState(state);
            }
        }
    };

    // Dummy constructor to use when extending class
    public LegacyUsbDeviceManager() {
        mContext = null;
        mContentResolver = null;
    }

    public LegacyUsbDeviceManager(Context context) {
        mContext = context;
        mContentResolver = context.getContentResolver();

        readOemUsbOverrideConfig();

        mHandler = new LegacyUsbHandler(FgThread.get().getLooper());

        boolean secureAdbEnabled = SystemProperties.getBoolean("ro.adb.secure", false);
        boolean dataEncrypted = "1".equals(SystemProperties.get("vold.decrypt"));
        if (secureAdbEnabled && !dataEncrypted) {
            mDebuggingManager = new UsbDebuggingManager(context);
        }
    }

    public void setCurrentSettings(UsbSettingsManager settings) {
        synchronized (mLock) {
            mCurrentSettings = settings;
        }
    }

    private UsbSettingsManager getCurrentSettings() {
        synchronized (mLock) {
            return mCurrentSettings;
        }
    }

    public void systemReady() {
        if (DEBUG) Slog.d(TAG, "systemReady");

        mNotificationManager = (NotificationManager)
                mContext.getSystemService(Context.NOTIFICATION_SERVICE);

        // We do not show the USB notification if the primary volume supports mass storage, unless
        // persist.sys.usb.config is set to mtp,adb. This will allow the USB notification to show
        // on devices with mtp as default and mass storage enabled on primary, so the user can choose
        // between mtp, ptp, and mass storage. The legacy mass storage UI will be used otherwise.
        boolean massStorageSupported = false;
        final StorageManager storageManager = StorageManager.from(mContext);
        final StorageVolume primary = storageManager.getPrimaryVolume();

        if (Settings.Secure.getInt(mContentResolver, Settings.Secure.USB_MASS_STORAGE_ENABLED, 0 ) == 1 ) {
                massStorageSupported = primary != null && primary.allowMassStorage();
        } else {
                massStorageSupported = false;
        }

        if ("mtp,adb".equals(SystemProperties.get("persist.sys.usb.config"))) {
            mUseUsbNotification = true;
        } else if (massStorageSupported) {
            mUseUsbNotification = true;
        } else {
            mUseUsbNotification = !massStorageSupported;
        }

        // make sure the ADB_ENABLED setting value matches the current state
        Settings.Global.putInt(mContentResolver, Settings.Global.ADB_ENABLED, mAdbEnabled ? 1 : 0);

        mHandler.sendEmptyMessage(MSG_SYSTEM_READY);
    }

     private static String addFunction(String functions, String function) {
         if ("none".equals(functions)) {
             return function;
         }
        if (!containsFunction(functions, function)) {
            if (functions.length() > 0) {
                functions += ",";
            }
            functions += function;
        }
        return functions;
    }

    private static String removeFunction(String functions, String function) {
        String[] split = functions.split(",");
        for (int i = 0; i < split.length; i++) {
            if (function.equals(split[i])) {
                split[i] = null;
            }
        }
        if (split.length == 1 && split[0] == null) {
            return "none";
        }
        StringBuilder builder = new StringBuilder();
         for (int i = 0; i < split.length; i++) {
            String s = split[i];
            if (s != null) {
                if (builder.length() > 0) {
                    builder.append(",");
                }
                builder.append(s);
            }
        }
        return builder.toString();
    }

    private static boolean containsFunction(String functions, String function) {
        int index = functions.indexOf(function);
        if (index < 0) return false;
        if (index > 0 && functions.charAt(index - 1) != ',') return false;
        int charAfter = index + function.length();
        if (charAfter < functions.length() && functions.charAt(charAfter) != ',') return false;
        return true;
    }

    private final class LegacyUsbHandler extends Handler {

        // current USB state
        private boolean mConnected;
        private boolean mConfigured;
        private String mCurrentFunctions;
        private String mDefaultFunctions;
        private int mUsbNotificationId;
        private int mAdbNotificationId;
        private int mCurrentUser = UserHandle.USER_NULL;

        private final BroadcastReceiver mBootCompletedReceiver = new BroadcastReceiver() {
            @Override
            public void onReceive(Context context, Intent intent) {
                if (DEBUG) Slog.d(TAG, "boot completed");
                mHandler.sendEmptyMessage(MSG_BOOT_COMPLETED);
            }
        };

        private final BroadcastReceiver mUserSwitchedReceiver = new BroadcastReceiver() {
            @Override
            public void onReceive(Context context, Intent intent) {
                final int userId = intent.getIntExtra(Intent.EXTRA_USER_HANDLE, -1);
                mHandler.obtainMessage(MSG_USER_SWITCHED, userId, 0).sendToTarget();
            }
        };

        public LegacyUsbHandler(Looper looper) {
            super(looper);
            char[] buffer = new char[1024];

            try {
                // persist.sys.usb.config should never be unset.  But if it is, set it to "adb"
                // so we have a chance of debugging what happened.
                mDefaultFunctions = SystemProperties.get("persist.sys.usb.config", "adb");

                // Check if USB mode needs to be overridden depending on OEM specific bootmode.
                mDefaultFunctions = processOemUsbOverride(mDefaultFunctions);

                // sanity check the sys.usb.config system property
                // this may be necessary if we crashed while switching USB configurations
                String config = SystemProperties.get("sys.usb.config", "none");
                if (!config.equals(mDefaultFunctions)) {
                    Slog.w(TAG, "resetting config to persistent property: " + mDefaultFunctions);
                    SystemProperties.set("sys.usb.config", mDefaultFunctions);
                }

                // Read initial USB state (device mode)
                try {
                    FileReader file = new FileReader(USB_CONNECTED_PATH);
                    int len = file.read(buffer, 0, 1024);
                    file.close();
                    mConnected = "1".equals((new String(buffer, 0, len)).trim());

                    file = new FileReader(USB_CONFIGURATION_PATH);
                    len = file.read(buffer, 0, 1024);
                    file.close();
                    mConfigured = "1".equals((new String(buffer, 0, len)).trim());
                } catch (FileNotFoundException e) {
                    Slog.i(TAG, "This kernel does not have USB configuration switch support");
                    Slog.i(TAG, "Trying legacy USB configuration switch support");
                    try {
                        FileReader file = new FileReader(USB_LEGACY_PATH);
                        int len = file.read(buffer, 0, 1024);
                        file.close();
                        mConnected = "online".equals((new String(buffer, 0, len)).trim());
                        mLegacy = true;
                        mConfigured = false;
                    } catch (FileNotFoundException f) {
                        Slog.i(TAG, "This kernel does not have legacy USB configuration switch support");
                    } catch (Exception f) {
                        Slog.e(TAG, "" , f);
                    }
                }

                mCurrentFunctions = mDefaultFunctions;
                String state;
                if (!mConnected && !mConfigured) state = "DISCONNECTED";
                else if(mConnected && !mConfigured) state =  "CONNECTED";
                else if(mConnected && mConfigured) state = "CONFIGURED";
                else state = "UNKNOWN";
                updateState(state);
                mAdbEnabled = containsFunction(mCurrentFunctions, UsbManager.USB_FUNCTION_ADB);

                // Upgrade step for previous versions that used persist.service.adb.enable
                String value = SystemProperties.get("persist.service.adb.enable", "");
                if (value.length() > 0) {
                    char enable = value.charAt(0);
                    if (enable == '1') {
                        setAdbEnabled(true);
                    } else if (enable == '0') {
                        setAdbEnabled(false);
                    }
                    SystemProperties.set("persist.service.adb.enable", "");
                }

                // register observer to listen for settings changes
                mContentResolver.registerContentObserver(
                        Settings.Global.getUriFor(Settings.Global.ADB_ENABLED),
                                false, new AdbSettingsObserver());

                ContentObserver adbNotificationObserver = new ContentObserver(null) {
                    @Override
                    public void onChange(boolean selfChange) {
                        updateAdbNotification();
                    }
                };
                mContentResolver.registerContentObserver(
                        Settings.Secure.getUriFor(Settings.Secure.ADB_PORT),
                                false, adbNotificationObserver);
                mContentResolver.registerContentObserver(
                        Settings.Secure.getUriFor(Settings.Secure.ADB_NOTIFY),
                                false, adbNotificationObserver);

                // Watch for USB configuration changes
                if (mLegacy) {
                    mUEventObserver.startObserving(USB_LEGACY_MATCH);
                } else {
                    mUEventObserver.startObserving(USB_CONNECTED_MATCH);
                    mUEventObserver.startObserving(USB_CONFIGURATION_MATCH);
                }

                mContext.registerReceiver(
                        mBootCompletedReceiver, new IntentFilter(Intent.ACTION_BOOT_COMPLETED));
                mContext.registerReceiver(
                        mUserSwitchedReceiver, new IntentFilter(Intent.ACTION_USER_SWITCHED));
            } catch (Exception e) {
                Slog.e(TAG, "Error initializing LegacyUsbHandler", e);
            }
        }

        public void sendMessage(int what, boolean arg) {
            removeMessages(what);
            Message m = Message.obtain(this, what);
            m.arg1 = (arg ? 1 : 0);
            sendMessage(m);
        }

        public void sendMessage(int what, Object arg) {
            removeMessages(what);
            Message m = Message.obtain(this, what);
            m.obj = arg;
            sendMessage(m);
        }

        public void sendMessage(int what, Object arg0, boolean arg1) {
            removeMessages(what);
            Message m = Message.obtain(this, what);
            m.obj = arg0;
            m.arg1 = (arg1 ? 1 : 0);
            sendMessage(m);
        }

        public void updateState(String state) {
            int connected, configured;

            if ("DISCONNECTED".equals(state)) {
                connected = 0;
                configured = 0;
            } else if ("CONNECTED".equals(state)) {
                connected = 1;
                configured = 0;
            } else if ("CONFIGURED".equals(state)) {
                connected = 1;
                configured = 1;
            } else {
                Slog.e(TAG, "unknown state " + state);
                return;
            }
            removeMessages(MSG_UPDATE_STATE);
            Message msg = Message.obtain(this, MSG_UPDATE_STATE);
            msg.arg1 = connected;
            msg.arg2 = configured;
            // debounce disconnects to avoid problems bringing up USB tethering
            sendMessageDelayed(msg, (connected == 0) ? UPDATE_DELAY : 0);
        }

        private boolean waitForState(String state) {
            // wait for the transition to complete.
            // give up after 1 second.
            for (int i = 0; i < 20; i++) {
                // State transition is done when sys.usb.state is set to the new configuration
                if (state.equals(SystemProperties.get("sys.usb.state"))) return true;
                SystemClock.sleep(50);
            }
            Slog.e(TAG, "waitForState(" + state + ") FAILED");
            return false;
        }

        private boolean setUsbConfig(String config) {
            if (DEBUG) Slog.d(TAG, "setUsbConfig(" + config + ")");
            // set the new configuration
            SystemProperties.set("sys.usb.config", config);
            return waitForState(config);
        }

        private void setAdbEnabled(boolean enable) {
            if (DEBUG) Slog.d(TAG, "setAdbEnabled: " + enable);
            if (enable != mAdbEnabled) {
                mAdbEnabled = enable;
                // Due to the persist.sys.usb.config property trigger, changing adb state requires
                // switching to default function
                setEnabledFunctions(mDefaultFunctions, true);
                updateAdbNotification();
            }
            if (mDebuggingManager != null) {
                mDebuggingManager.setAdbEnabled(mAdbEnabled);
            }
        }

        private void setEnabledFunctions(String functions, boolean makeDefault) {
            if (DEBUG) Slog.d(TAG, "setEnabledFunctions " + functions
                    + " makeDefault: " + makeDefault);

            // Do not update persystent.sys.usb.config if the device is booted up
            // with OEM specific mode.
            if (functions != null && makeDefault && !needsOemUsbOverride()) {

                if (mAdbEnabled) {
                    functions = addFunction(functions, UsbManager.USB_FUNCTION_ADB);
                } else {
                    functions = removeFunction(functions, UsbManager.USB_FUNCTION_ADB);
                }
                if (!mDefaultFunctions.equals(functions)) {
                    if (!setUsbConfig("none")) {
                        Slog.e(TAG, "Failed to disable USB");
                        // revert to previous configuration if we fail
                        setUsbConfig(mCurrentFunctions);
                        return;
                    }
                    // setting this property will also change the current USB state
                    // via a property trigger
                    SystemProperties.set("persist.sys.usb.config", functions);
                    if (waitForState(functions)) {
                        mCurrentFunctions = functions;
                        mDefaultFunctions = functions;
                    } else {
                        Slog.e(TAG, "Failed to switch persistent USB config to " + functions);
                        // revert to previous configuration if we fail
                        SystemProperties.set("persist.sys.usb.config", mDefaultFunctions);
                    }
                }
            } else {
                if (functions == null) {
                    functions = mDefaultFunctions;
                }

                // Override with bootmode specific usb mode if needed
                functions = processOemUsbOverride(functions);

                if (mAdbEnabled) {
                    functions = addFunction(functions, UsbManager.USB_FUNCTION_ADB);
                } else {
                    functions = removeFunction(functions, UsbManager.USB_FUNCTION_ADB);
                }
                if (!mCurrentFunctions.equals(functions)) {
                    if (!setUsbConfig("none")) {
                        Slog.e(TAG, "Failed to disable USB");
                        // revert to previous configuration if we fail
                        setUsbConfig(mCurrentFunctions);
                        return;
                    }
                    if (setUsbConfig(functions)) {
                        mCurrentFunctions = functions;
                    } else {
                        Slog.e(TAG, "Failed to switch USB config to " + functions);
                        // revert to previous configuration if we fail
                        setUsbConfig(mCurrentFunctions);
                    }
                }
            }
        }

        private void updateUsbState() {
            // send a sticky broadcast containing current USB state
            Intent intent = new Intent(UsbManager.ACTION_USB_STATE);
            intent.addFlags(Intent.FLAG_RECEIVER_REPLACE_PENDING);
            intent.putExtra(UsbManager.USB_CONNECTED, mConnected);
            intent.putExtra(UsbManager.USB_CONFIGURED, mConfigured);

            if (mCurrentFunctions != null) {
                String[] functions = mCurrentFunctions.split(",");
                for (int i = 0; i < functions.length; i++) {
                    intent.putExtra(functions[i], true);
                }
            }

            if (DEBUG) Slog.d(TAG, "broadcasting " + intent + " connected: " + mConnected
                                    + " configured: " + mConfigured);
            mContext.sendStickyBroadcastAsUser(intent, UserHandle.ALL);
        }

        @Override
        public void handleMessage(Message msg) {
            switch (msg.what) {
                case MSG_UPDATE_STATE:
                    mConnected = (msg.arg1 == 1);
                    mConfigured = (msg.arg2 == 1);
                    updateUsbNotification();
                    updateAdbNotification();
                    if (!mConnected) {
                        // restore defaults when USB is disconnected
                        setEnabledFunctions(mDefaultFunctions, false);
                    }
                    if (mBootCompleted) {
                        updateUsbState();
                    }
                    break;
                case MSG_ENABLE_ADB:
                    setAdbEnabled(msg.arg1 == 1);
                    break;
                case MSG_SET_CURRENT_FUNCTIONS:
                    String functions = (String)msg.obj;
                    boolean makeDefault = (msg.arg1 == 1);
                    setEnabledFunctions(functions, makeDefault);
                    break;
                case MSG_SYSTEM_READY:
                    updateUsbNotification();
                    updateAdbNotification();
                    updateUsbState();
                    break;
                case MSG_BOOT_COMPLETED:
                    mBootCompleted = true;
                    if (mDebuggingManager != null) {
                        mDebuggingManager.setAdbEnabled(mAdbEnabled);
                    }
                    break;
                case MSG_USER_SWITCHED: {
                    final boolean mtpActive =
                            containsFunction(mCurrentFunctions, UsbManager.USB_FUNCTION_MTP)
                            || containsFunction(mCurrentFunctions, UsbManager.USB_FUNCTION_PTP);
                    if (mtpActive && mCurrentUser != UserHandle.USER_NULL) {
                        Slog.v(TAG, "Current user switched; resetting USB host stack for MTP");
                        setUsbConfig("none");
                        setUsbConfig(mCurrentFunctions);
                    }
                    mCurrentUser = msg.arg1;
                    break;
                }
            }
        }

        private void updateUsbNotification() {
            if (mNotificationManager == null || !mUseUsbNotification) return;
            int id = 0;
            Resources r = mContext.getResources();
            if (mConnected) {
                if (containsFunction(mCurrentFunctions, UsbManager.USB_FUNCTION_MTP)) {
                    id = com.android.internal.R.string.usb_mtp_notification_title;
                } else if (containsFunction(mCurrentFunctions, UsbManager.USB_FUNCTION_PTP)) {
                    id = com.android.internal.R.string.usb_ptp_notification_title;
                } /* else if (containsFunction(mCurrentFunctions,
                        UsbManager.USB_FUNCTION_MASS_STORAGE)) { // Disable this as it causes double USB settings menues when in UMS mode.
                    id = com.android.internal.R.string.usb_cd_installer_notification_title;
                } */ else {
                    // There is a different notification for USB tethering so we don't need one here
                    //if (!containsFunction(mCurrentFunctions, UsbManager.USB_FUNCTION_RNDIS)) {
                    //    Slog.e(TAG, "No known USB function in updateUsbNotification");
                    //}
                }
            }
            if (id != mUsbNotificationId) {
                // clear notification if title needs changing
                if (mUsbNotificationId != 0) {
                    mNotificationManager.cancelAsUser(null, mUsbNotificationId,
                            UserHandle.ALL);
                    mUsbNotificationId = 0;
                }
                if (id != 0) {
                    CharSequence message = r.getText(
                            com.android.internal.R.string.usb_notification_message);
                    CharSequence title = r.getText(id);

                    Notification notification = new Notification();
                    notification.icon = com.android.internal.R.drawable.stat_sys_data_usb;
                    notification.when = 0;
                    notification.flags = Notification.FLAG_ONGOING_EVENT;
                    notification.tickerText = title;
                    notification.defaults = 0; // please be quiet
                    notification.sound = null;
                    notification.vibrate = null;
                    notification.priority = Notification.PRIORITY_MIN;

                    Intent intent = Intent.makeRestartActivityTask(
                            new ComponentName("com.android.settings",
                                    "com.android.settings.UsbSettings"));
                    PendingIntent pi = PendingIntent.getActivityAsUser(mContext, 0,
                            intent, 0, null, UserHandle.CURRENT);
                    notification.setLatestEventInfo(mContext, title, message, pi);
                    mNotificationManager.notifyAsUser(null, id, notification,
                            UserHandle.ALL);
                    mUsbNotificationId = id;
                }
            }
        }


        private void updateAdbNotification() {
            if (mNotificationManager == null) return;
            boolean usbAdbActive = mAdbEnabled && mConnected;
            boolean netAdbActive = mAdbEnabled &&
                    Settings.Secure.getInt(mContentResolver, Settings.Secure.ADB_PORT, -1) > 0;
            final int id;

            if ("0".equals(SystemProperties.get("persist.adb.notify"))) {
                id = 0;
            } else if (Settings.Secure.getInt(mContentResolver,
                    Settings.Secure.ADB_NOTIFY, 1) == 0) {
                id = 0;
            } else if (usbAdbActive && netAdbActive) {
                id = com.android.internal.R.string.adb_both_active_notification_title;
            } else if (usbAdbActive) {
                id = com.android.internal.R.string.adb_active_notification_title;
            } else if (netAdbActive) {
                id = com.android.internal.R.string.adb_net_active_notification_title;
            } else {
                id = 0;
            }

            if (id != mAdbNotificationId) {
                if (mAdbNotificationId != 0) {
                    mNotificationManager.cancelAsUser(null, mAdbNotificationId, UserHandle.ALL);
                }
                if (id != 0) {
                    Resources r = mContext.getResources();
                    CharSequence title = r.getText(id);
                    CharSequence message = r.getText(
                            com.android.internal.R.string.adb_active_generic_notification_message);
                    Notification notification = new Notification();
                    notification.icon = com.android.internal.R.drawable.stat_sys_adb;
                    notification.when = 0;
                    notification.flags = Notification.FLAG_ONGOING_EVENT;
                    notification.tickerText = title;
                    notification.defaults = 0; // please be quiet
                    notification.sound = null;
                    notification.vibrate = null;
                    notification.priority = Notification.PRIORITY_LOW;

                    Intent intent = Intent.makeRestartActivityTask(
                            new ComponentName("com.android.settings",
                                    "com.android.settings.DevelopmentSettings"));
                    PendingIntent pi = PendingIntent.getActivityAsUser(mContext, 0,
                            intent, 0, null, UserHandle.CURRENT);
                    notification.setLatestEventInfo(mContext, title, message, pi);
                    mNotificationManager.notifyAsUser(null, id, notification, UserHandle.ALL);
                }
                mAdbNotificationId = id;
            }
        }

        public void dump(FileDescriptor fd, PrintWriter pw) {
            pw.println("  USB Device State:");
            pw.println("    Current Functions: " + mCurrentFunctions);
            pw.println("    Default Functions: " + mDefaultFunctions);
            pw.println("    mConnected: " + mConnected);
            pw.println("    mConfigured: " + mConfigured);
            try {
                pw.println("    Kernel state: "
                        + FileUtils.readTextFile(new File(USB_CONNECTED_PATH), 0, null).trim());
                pw.println("    Kernel function list: "
               + Arrays.toString(new File(FUNCTIONS_PATH).list()));
                pw.println("    Mass storage backing file: "
                        + FileUtils.readTextFile(new File(MASS_STORAGE_FILE_PATH), 0, null).trim());
            } catch (IOException e) {
                pw.println("IOException: " + e);
            }
        }
    }

    public void setCurrentFunctions(String functions, boolean makeDefault) {
        if (DEBUG) Slog.d(TAG, "setCurrentFunctions(" + functions + ") default: " + makeDefault);
        mHandler.sendMessage(MSG_SET_CURRENT_FUNCTIONS, functions, makeDefault);
    }

    public void setMassStorageBackingFile(String path) {
        if (path == null) path = "";
        try {
            FileUtils.stringToFile(MASS_STORAGE_FILE_PATH, path);
        } catch (IOException e) {
           Slog.e(TAG, "failed to write to " + MASS_STORAGE_FILE_PATH);
        }
    }

    private void readOemUsbOverrideConfig() {
        String[] configList = mContext.getResources().getStringArray(
            com.android.internal.R.array.config_oemUsbModeOverride);

        if (configList != null) {
            for (String config: configList) {
                String[] items = config.split(":");
                if (items.length == 3) {
                    if (mOemModeMap == null) {
                        mOemModeMap = new HashMap<String, List<Pair<String, String>>>();
                    }
                    List overrideList = mOemModeMap.get(items[0]);
                    if (overrideList == null) {
                        overrideList = new LinkedList<Pair<String, String>>();
                        mOemModeMap.put(items[0], overrideList);
                    }
                    overrideList.add(new Pair<String, String>(items[1], items[2]));
                }
            }
        }
    }

    private boolean needsOemUsbOverride() {
        if (mOemModeMap == null) return false;

        String bootMode = SystemProperties.get(BOOT_MODE_PROPERTY, "unknown");
        return (mOemModeMap.get(bootMode) != null) ? true : false;
    }

    private String processOemUsbOverride(String usbFunctions) {
        if ((usbFunctions == null) || (mOemModeMap == null)) return usbFunctions;

        String bootMode = SystemProperties.get(BOOT_MODE_PROPERTY, "unknown");

        List<Pair<String, String>> overrides = mOemModeMap.get(bootMode);
        if (overrides != null) {
            for (Pair<String, String> pair: overrides) {
                if (pair.first.equals(usbFunctions)) {
                    Slog.d(TAG, "OEM USB override: " + pair.first + " ==> " + pair.second);
                    return pair.second;
                }
            }
        }
        // return passed in functions as is.
        return usbFunctions;
    }

    public void allowUsbDebugging(boolean alwaysAllow, String publicKey) {
        if (mDebuggingManager != null) {
            mDebuggingManager.allowUsbDebugging(alwaysAllow, publicKey);
        }
    }

    public void denyUsbDebugging() {
        if (mDebuggingManager != null) {
            mDebuggingManager.denyUsbDebugging();
        }
    }

    public void clearUsbDebuggingKeys() {
        if (mDebuggingManager != null) {
            mDebuggingManager.clearUsbDebuggingKeys();
        } else {
            throw new RuntimeException("Cannot clear Usb Debugging keys, "
                        + "UsbDebuggingManager not enabled");
        }
    }

    public void dump(FileDescriptor fd, PrintWriter pw) {
        if (mHandler != null) {
            mHandler.dump(fd, pw);
        }
        if (mDebuggingManager != null) {
            mDebuggingManager.dump(fd, pw);
        }
    }

}
