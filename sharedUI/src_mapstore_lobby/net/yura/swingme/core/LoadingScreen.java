package net.yura.swingme.core;

import net.yura.mobile.gui.Application;
import net.yura.mobile.gui.components.Label;
import net.yura.mobile.gui.components.ProgressBar;
import net.yura.mobile.gui.components.Window;
import net.yura.mobile.util.Url;
import javax.microedition.lcdui.Graphics;

public class LoadingScreen {

    private static Window instance;

    public static void show(String message) {

        if (Application.getPlatform() == Application.PLATFORM_ANDROID) {
            Application.openURL("nativeNoResult://net.yura.android.LoadingDialog?message=" + Url.encode(message));
            return;
        }

        if (instance == null) {
            instance = new Window();
            instance.setName("OpaqueDialog");

            final ProgressBar bar = new ProgressBar();
            bar.setIndeterminate(true);

            instance.add(bar);
            instance.add(new Label(message), Graphics.RIGHT);
            instance.pack();
            instance.setLocationRelativeTo(null);
        }

        instance.setVisible(true);
    }

    public static void hide() {

        if (Application.getPlatform() == Application.PLATFORM_ANDROID) {
            Application.openURL("nativeNoResult://net.yura.android.LoadingDialog?command=hide");
            return;
        }

        Window window = instance;
        if (window != null) {
            window.setVisible(false);
        }

        instance = null;
    }
}
