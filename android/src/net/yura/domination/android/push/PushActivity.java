package net.yura.domination.android.push;

import java.util.logging.Level;
import android.app.Activity;
import android.os.Bundle;
import net.yura.android.AndroidMeApp;
import net.yura.domination.mobile.flashgui.DominationMain;
import net.yura.domination.mobile.flashgui.MiniFlashRiskAdapter;
import net.yura.lobby.client.Connection;
import net.yura.lobby.mini.MiniLobbyClient;

/**
 * this activity is started when we connect to the lobby server
 */
public class PushActivity extends Activity {

    @Override
    public void onCreate(Bundle savedInstanceState) {
	super.onCreate(savedInstanceState);
	try {
            FCMServerUtilities.setup();
	}
	catch (Throwable th) {
            FCMServerUtilities.logger.log(Level.WARNING, "FCM fail", th);
	}

        try {
            //ADMServerUtilities.setup();
        }
        catch (Throwable th) {
            ADMServerUtilities.logger.log(Level.WARNING, "ADM fail", th);
        }

        finish();
    }

    public static Connection getLobbyConnection() {
        DominationMain main = (DominationMain)AndroidMeApp.getMIDlet();
        if (main != null) {
            MiniFlashRiskAdapter gui = main.adapter;
            if (gui != null) {
                MiniLobbyClient lobby = gui.lobby;
                if (lobby != null) {
                    return lobby.mycom;
                }
            }
        }
        return null;
    }
}
