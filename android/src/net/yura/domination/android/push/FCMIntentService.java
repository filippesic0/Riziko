package net.yura.domination.android.push;

import java.util.Collections;
import java.util.HashMap;
import java.util.Map;
import java.util.logging.Level;
import javax.microedition.midlet.MIDlet;
import net.yura.domination.R;
import net.yura.lobby.client.PushLobbyClient;
import net.yura.lobby.mini.MiniLobbyClient;
import com.google.firebase.messaging.FirebaseMessagingService;
import com.google.firebase.messaging.RemoteMessage;
import androidx.annotation.NonNull;

public class FCMIntentService extends FirebaseMessagingService {

    /**
     * This gets called from inside the FirebaseMessagingService, so we dont want to throw into there.
     */
    @Override
    public void onNewToken(@NonNull String registrationId) {
        try {
            FCMServerUtilities.logger.info("Device registered: regId = " + registrationId);
            FCMRegistrar.setRegisteredOnServer(null);
            FCMServerUtilities.registerOnLobbyServer(registrationId);
        }
        catch (Exception ex) {
            FCMServerUtilities.logger.log(Level.WARNING, "failed to handle onNewToken " + registrationId, ex);
        }
    }

    /**
     * @see MiniLobbyClient#notify(net.yura.lobby.model.Game, boolean)
     */
    @Override
    public void onMessageReceived(@NonNull RemoteMessage remoteMessage){
        String from = remoteMessage.getFrom();
        Map<String, String> data = remoteMessage.getData();

        String msg = data.get(PushLobbyClient.MESSAGE);
        String gameId = data.get(PushLobbyClient.GAME_ID);
        String options = data.get(PushLobbyClient.OPTIONS);

        String message = msg==null?"Received message":msg;
        FCMServerUtilities.logger.info(from + ": " + message);
        // notifies user
        Map<String, Object> extras = new HashMap();

        if (gameId != null) {
            extras.put(PushLobbyClient.GAME_ID, gameId);
        }
        if (options != null) {
            extras.put(PushLobbyClient.OPTIONS, options);
        }
        MIDlet.showNotification(this.getString(R.string.app_name), message, R.drawable.icon, -1, extras);
    }

    @Override
    public void onDeletedMessages() {
        String message = "Received deleted messages notification ";
        FCMServerUtilities.logger.info(message);
        // notifies user
        MIDlet.showNotification(this.getString(R.string.app_name), message, R.drawable.icon, -1, Collections.EMPTY_MAP);
    }

    @Override
    public void onSendError(@NonNull String s, @NonNull Exception ex) {
        FCMServerUtilities.logger.info("Received error: " + s + " " + ex);
    }

    @Override
    public void onMessageSent(@NonNull String s) {
        FCMServerUtilities.logger.info("onMessageSent: "+s);
    }
}
