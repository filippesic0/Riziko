package net.yura.domination.android.push;

import android.content.Context;
import android.content.SharedPreferences;
import android.preference.PreferenceManager;
import net.yura.android.AndroidPreferences;
import java.util.prefs.Preferences;

/**
 * @see com.google.android.gcm.GCMRegistrar
 */
public class FCMRegistrar {

    public static final long DEFAULT_ON_SERVER_LIFESPAN_MS = 604800000L; // 7 days

    private static final String KEY = "onServerToken";
    private static final String PROPERTY_ON_SERVER_EXPIRATION_TIME = "onServerExpirationTime";

    /**
     * onNewToken may be called when the app is not running and there is no activity
     * so we do not want to use the ones in DominationMain as that may be null
     * @see net.yura.domination.mobile.flashgui.DominationMain#appPreferences
     */
    private static Preferences getFCMPreferences() {
        Context context = net.yura.android.AndroidMeApp.getContext();
        SharedPreferences sharedPreferences = PreferenceManager.getDefaultSharedPreferences(context);
        return new AndroidPreferences(sharedPreferences);
    }

    /**
     * @see com.google.android.gcm.GCMRegistrar#isRegisteredOnServer(Context)
     */
    public static boolean isRegisteredOnServer(String token) {
        Preferences preferences = getFCMPreferences();

        String dbtoken = preferences.get(KEY, null);
        if (token == null) {
            // if token is null we want to find out if we are registered on the server at all
            return dbtoken != null;
        }
        boolean isRegistered = token.equals(dbtoken);
        if (isRegistered) {
            long expirationTime = preferences.getLong(PROPERTY_ON_SERVER_EXPIRATION_TIME, -1L);
            if (System.currentTimeMillis() > expirationTime) {
                return false;
            }
        }
        return isRegistered;
    }

    /**
     * @see com.google.android.gcm.GCMRegistrar#setRegisteredOnServer(Context, boolean)
     */
    public static void setRegisteredOnServer(String token) {
        Preferences preferences = getFCMPreferences();

        if (token == null) {
            preferences.remove(KEY);
            preferences.remove(PROPERTY_ON_SERVER_EXPIRATION_TIME);
        }
        else {
            preferences.put(KEY, token);
            preferences.putLong(PROPERTY_ON_SERVER_EXPIRATION_TIME, System.currentTimeMillis() + DEFAULT_ON_SERVER_LIFESPAN_MS);
        }
        try {
            preferences.flush();
        }
        catch (Exception ex) {
            ex.printStackTrace();
        }
    }
}
