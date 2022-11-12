package net.yura.domination.android.push;

import java.util.Collections;
import java.util.HashMap;
import java.util.Map;
import javax.microedition.midlet.MIDlet;
import net.yura.android.AndroidMeApp;
import net.yura.domination.R;
import net.yura.lobby.client.PushLobbyClient;
import net.yura.lobby.mini.MiniLobbyClient;
import android.content.Context;
import android.content.Intent;
import android.os.Bundle;
import com.google.android.gcm.GCMBaseIntentService;
import com.google.android.gcm.GCMRegistrar;

/**
 * @see com.google.android.gcm.demo.app.GCMIntentService
 */
public class ADMIntentService extends GCMBaseIntentService {

    public ADMIntentService() {
        super(AndroidMeApp.getContext().getString(R.string.app_id));
    }

    @Override
    protected void onRegistered(Context context, String registrationId) {
        ADMServerUtilities.logger.info("Device registered: regId = "+registrationId);
        ADMServerUtilities.registerOnLobbyServer(context, registrationId);
    }

    @Override
    protected void onUnregistered(Context context, String registrationId) {
        ADMServerUtilities.logger.info("Device unregistered");
        if (GCMRegistrar.isRegisteredOnServer(context)) {
            ADMServerUtilities.unregisterOnLobbyServer(context, registrationId);
        } else {
            // This callback results from the call to unregister made on
            // ServerUtilities when the registration to the server failed.
            ADMServerUtilities.logger.info("Ignoring unregister callback");
        }
    }

    /**
     * @see MiniLobbyClient#notify(net.yura.lobby.model.Game, boolean)
     */
    @Override
    protected void onMessage(Context context, Intent intent) {
        Bundle bundle = intent.getExtras();
        String msg=null, gameId=null, options=null;
        if (bundle != null) {
            msg = bundle.getString(PushLobbyClient.MESSAGE);
            gameId = bundle.getString(PushLobbyClient.GAME_ID);
            options = bundle.getString(PushLobbyClient.OPTIONS);
        }

        String message = msg==null?"Received message":msg;
        ADMServerUtilities.logger.info(message);
        // notifies user
        Map<String, Object> extras = new HashMap();
        if (gameId != null) {
            extras.put(PushLobbyClient.GAME_ID, gameId);
        }
        if (options != null) {
            extras.put(PushLobbyClient.OPTIONS, options);
        }
        MIDlet.showNotification(context.getString(R.string.app_name), message, R.drawable.icon, -1, extras);
    }

    @Override
    protected void onDeletedMessages(Context context, int total) {
        String message = "Received deleted messages notification "+total;
        ADMServerUtilities.logger.info(message);
        // notifies user
        MIDlet.showNotification(context.getString(R.string.app_name), message, R.drawable.icon, -1, Collections.EMPTY_MAP);
    }

    @Override
    public void onError(Context context, String errorId) {
        ADMServerUtilities.logger.info("Received error: "+errorId);
    }

    @Override
    protected boolean onRecoverableError(Context context, String errorId) {
        // log message
        ADMServerUtilities.logger.info("Received recoverable error: "+errorId);
        return super.onRecoverableError(context, errorId);
    }
}
