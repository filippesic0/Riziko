package net.yura.domination.android.push;

import android.content.Context;

public class ADMBroadcastReceiver extends com.google.android.gcm.GCMBroadcastReceiver {

    @Override
    protected String getGCMIntentServiceClassName(Context context) {
        return ADMIntentService.class.getName();
    }
    
}
