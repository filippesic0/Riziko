package net.yura.domination.android.push;

import java.util.logging.Level;
import java.util.logging.Logger;
import android.widget.Toast;
import androidx.annotation.NonNull;
import com.google.android.gms.tasks.OnCompleteListener;
import com.google.android.gms.tasks.Task;
import com.google.firebase.messaging.FirebaseMessaging;
import net.yura.lobby.client.Connection;
import net.yura.lobby.client.PushLobbyClient;

public class FCMServerUtilities implements PushLobbyClient {

    static final Logger logger = Logger.getLogger(FCMServerUtilities.class.getName());

    public static void setup() {

        // can not use this check as sometimes even if this is not SUCCESS, push still works fine
        //if (GoogleApiAvailability.getInstance().isGooglePlayServicesAvailable(this) == ConnectionResult.SUCCESS) {

        FirebaseMessaging.getInstance().getToken()
                .addOnCompleteListener(new OnCompleteListener<String>() {
                    @Override
                    public void onComplete(@NonNull Task<String> task) {
                        if (!task.isSuccessful()) {
                            // something went wrong, should we request to register? it should do this automatically
                            // FirebaseMessaging.getInstance().setAutoInitEnabled(true);

                            Exception exception = task.getException();
                            Level level = Level.WARNING;
                            // for some strange reason this comes back as IOException
                            if (exception != null && (
                                    // this is returned when GMS is not installed
                                    "MISSING_INSTANCEID_SERVICE".equals(exception.getMessage()) ||

                                    // this can happen when the phones date/time is incorrect
                                    // TODO maybe prompt user to check phone date/time
                                    // TODO also some report that retrying can fix this issue
                                    "SERVICE_NOT_AVAILABLE".equals(exception.getMessage())
                            )) {
                                level = Level.INFO;
                            }

                            if (exception != null && "TOO_MANY_REGISTRATIONS".equals(exception.getMessage())) {
                                if (net.yura.android.AndroidMeActivity.DEFAULT_ACTIVITY != null) {
                                    javax.microedition.midlet.MIDlet.showToast("FCM Error: TOO_MANY_REGISTRATIONS, try uninstalling some apps for notifications to work", Toast.LENGTH_LONG);
                                }
                            }

                            logger.log(level, "Fetching FCM registration token failed", exception);
                            return;
                        }

                        // Get new Instance ID token
                        String token = task.getResult();

                        if (FCMRegistrar.isRegisteredOnServer(token)) {
                            logger.info("FCM Already registered");
                        }
                        else {
                            FCMServerUtilities.registerOnLobbyServer(token);
                        }
                    }
                });
    }

    public static void delete() {

        // not really sure this is correct, but its not currently used, so who cares
        FirebaseMessaging.getInstance().deleteToken()
                .addOnCompleteListener(new OnCompleteListener<Void>() {
                    @Override
                    public void onComplete(@NonNull Task<Void> task) {
                        if (!task.isSuccessful()) {
                            logger.log(Level.WARNING, "FCM deleteToken failed", task.getException());
                            return;
                        }

                        logger.info("FCM Device unregistered");
                        if (FCMRegistrar.isRegisteredOnServer(null)) {
                            FCMServerUtilities.unregisterOnLobbyServer();
                        }
                        else {
                            // This callback results from the call to unregister made on
                            // ServerUtilities when the registration to the server failed.
                            logger.info("FCM Ignoring unregister callback");
                        }
                    }
                });
    }






    public static void registerOnLobbyServer(String registrationId) {
        Connection con = PushActivity.getLobbyConnection();
        if (con != null) {
            con.addPushEventListener(new FCMServerUtilities(registrationId));
            con.setPushToken(PUSH_SYSTEM_FCM, registrationId);
        }
    }

    public static void unregisterOnLobbyServer() {
        Connection con = PushActivity.getLobbyConnection();
        if (con != null) {
            con.addPushEventListener(new FCMServerUtilities(null));
            con.setPushToken(PUSH_SYSTEM_FCM, null);
        }
    }

    String token;
    public FCMServerUtilities(String token) {
        this.token = token;
    }

    @Override
    public void registerDone() {
        FCMRegistrar.setRegisteredOnServer(token);
    }
}
