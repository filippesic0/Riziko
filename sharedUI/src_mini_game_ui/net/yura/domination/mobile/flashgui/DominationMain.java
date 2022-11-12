package net.yura.domination.mobile.flashgui;

import java.io.File;
import java.io.InputStream;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.logging.Handler;
import java.util.logging.Level;
import java.util.logging.LogRecord;
import java.util.logging.Logger;
import java.util.prefs.Preferences;
import net.yura.domination.engine.Risk;
import net.yura.domination.engine.RiskUtil;
import net.yura.domination.engine.ai.AIManager;
import net.yura.domination.engine.core.RiskGame;
import net.yura.domination.engine.translation.TranslationBundle;
import net.yura.domination.mapstore.MapChooser;
import net.yura.domination.mapstore.MapUpdateService;
import net.yura.domination.mobile.MiniUtil;
import net.yura.domination.mobile.RiskMiniIO;
import net.yura.grasshopper.ApplicationInfoProvider;
import net.yura.grasshopper.BugSubmitter;
import net.yura.grasshopper.LogList;
import net.yura.grasshopper.SimpleBug;
import net.yura.lobby.client.PushLobbyClient;
import net.yura.lobby.mini.MiniLobbyClient;
import net.yura.lobby.model.Game;
import net.yura.mobile.gui.Application;
import net.yura.mobile.gui.DesktopPane;
import net.yura.mobile.gui.Graphics2D;
import net.yura.mobile.gui.Icon;
import net.yura.mobile.gui.components.Component;
import net.yura.mobile.gui.components.OptionPane;
import net.yura.mobile.gui.plaf.Style;
import net.yura.mobile.gui.plaf.SynthLookAndFeel;
import net.yura.mobile.gui.plaf.nimbus.NimbusLookAndFeel;
import net.yura.swingme.core.J2SELogger;
import net.yura.util.Service;

/**
 * This class is instantiated by the AndroidMEApp even if there is no AndroidMEActivity
 */
public class DominationMain extends Application {

    private static final Logger logger = Logger.getLogger(DominationMain.class.getName());

    public static final boolean DEFAULT_SHOW_DICE = true;
    public static final String SHOW_DICE_KEY = "show_dice";

    public static final String DEFAULT_GAME_TYPE_KEY = "default.gametype";
    public static final String DEFAULT_CARD_TYPE_KEY = "default.cardtype";
    public static final String DEFAULT_AUTO_PLACE_ALL_KEY = "default.autoplaceall";
    public static final String DEFAULT_RECYCLE_CARDS_KEY = "default.recycle";

    /**
     * @see net.yura.domination.ui.flashgui.MainMenu#product
     */
    public static final String product;
    public static final String version;
    static {
        if (Application.getPlatform() == Application.PLATFORM_IOS) {
            product = "iOS-GUI";
        }
        else if (Application.getPlatform() == Application.PLATFORM_ANDROID) {
            product = "AndroidGUI";
        }
        else {
            product = "MiniGameGUI";
        }

        String versionCode = System.getProperty("versionCode");
        version = versionCode != null ? versionCode : RiskUtil.RISK_VERSION;
    }

    public static Preferences appPreferences = Preferences.userNodeForPackage(DominationMain.class);
    public GooglePlayGameServices googlePlayGameServices;

    public Risk risk;
    public MiniFlashRiskAdapter adapter;

    public interface GooglePlayGameServices {
	void beginUserInitiatedSignIn();
	void signOut();
	boolean isSignedIn();

	void showAchievements();
        void unlockAchievement(String id);

        /**
         * @deprecated
         */
	void startGameGooglePlay(net.yura.lobby.model.Game game);
        /**
         * @deprecated
         */
	void setLobbyUsername(String username);
        /**
         * @deprecated
         */
	void gameStarted(int id);
    }

    public DominationMain() {

        if (Application.getPlatform() == Application.PLATFORM_ANDROID) {
            Service.SERVICES_LOCATION = "assets/services/";
        }

        // IO depends on this, so we need to do this first
        RiskUtil.streamOpener = new RiskMiniIO();

        // get version from AndroidManifest.xml
        //String versionName = System.getProperty("versionName");
        //Risk.RISK_VERSION = versionName!=null ? versionName : "?me4se?";

        try {
            SimpleBug.initLogFile(RiskUtil.GAME_NAME + " " + product, version, TranslationBundle.getBundle().getLocale().toString());
            BugSubmitter.setApplicationInfoProvider( new ApplicationInfoProvider() {
                /**
                 * info specific to Domination goes here, for general android system info look in:
                 * @see net.yura.android.AndroidMeApp#setSystemProperties()
                 */
                @Override
                public void addInfoForSubmit(Map map) {
                    Risk r = risk;
                    if (r != null) {
                        RiskGame game = r.getGame();
                        if (game != null) {
                            map.put("gameLog", new LogList( game.getCommands() ));
                        }
                    }

                    if (adapter != null && adapter.email != null) {
                        map.put("email", adapter.email);
                    }

                    map.put("lobbyID", MiniLobbyClient.getMyUUID() );
                }
                @Override
                public boolean ignoreError(LogRecord record) {
                    if (RiskUtil.isOldVersion()) {
                        return true;
                    }
                    String loggerName = record.getLoggerName();
                    if ("DataScheduler".equals(loggerName)) { // "libcore.io.IoBridge".equals(className) && "isDataSchedulerEnabled".equals(methodName)
                        // isDataSchedulerEnabled(): DataScheduler is disabled, exeption=java.io.FileNotFoundException: /system/etc/datascheduling_policy_conf.xml: open failed: ENOENT (No such file or directory)
                        return true;
                    }

                    String className = record.getSourceClassName();
                    String methodName = record.getSourceMethodName();
                    if ("java.net.InetAddress".equals(className) && "lookupHostByName".equals(methodName)) {
                        return true;
                    }
                    if ("java.net.InetAddress".equals(className) && "getByName".equals(methodName)) {
                        return true;
                    }
                    if ("java.net.AddressCache".equals(className) && "customTtl".equals(methodName)) {
                        return true;
                    }
                    if ("java.util.prefs.FileSystemPreferences".equals(className) && "loadCache".equals(methodName)) {
                        // Exception while reading cache: Attempt to invoke interface method 'java.lang.String org.w3c.dom.Element.getAttribute(java.lang.String)' on a null object reference
                        return true;
                    }

                    String message = record.getMessage();
                    if ("rto value is too small:0".equals(message) ||
                        "/data/system/carrierinfo.prop: open failed: ENOENT (No such file or directory)".equals(message) ||
                        "isDataSchedulerEnabled():false".equals(message) ||
                        "remove failed: ENOENT (No such file or directory) : /data/data/net.yura.domination/shared_prefs/net.yura.domination_preferences.xml.bak".equals(message) ||
                        "remove failed: ENOENT (No such file or directory) : /data/data/net.yura.domination/shared_prefs/com.google.android.gcm.xml.bak".equals(message) ||
                        "remove failed: ENOENT (No such file or directory) : /data/user/0/net.yura.domination/shared_prefs/net.yura.domination_preferences.xml.bak".equals(message) ||
                        "remove failed: ENOENT (No such file or directory) : /data/user/0/net.yura.domination/shared_prefs/com.google.android.gcm.xml.bak".equals(message) ||
                        "remove failed: ENOENT (No such file or directory) : /data/user/0/net.yura.domination/shared_prefs/com.google.android.gms.signin.xml.bak".equals(message) ||
                        "remove failed: ENOENT (No such file or directory) : /data/user/0/net.yura.domination/shared_prefs/com.google.android.gms.appid.xml.bak".equals(message) ||
                        "remove failed: ENOENT (No such file or directory) : /data/user/0/net.yura.domination/shared_prefs/FirebaseAppHeartBeat.xml.bak".equals(message) ||
                        "mkdir failed: EEXIST (File exists) : /data/user/0/net.yura.domination/cache/WebView/Crash Reports".equals(message) ||
                        "mkdir failed: EEXIST (File exists) : /data/data/net.yura.domination/cache/WebView/Crash Reports".equals(message) ||
                        "stat failed: ENOENT (No such file or directory) : /data/data/net.yura.domination/files/assetpacks".equals(message) ||
                        "stat failed: ENOENT (No such file or directory) : /data/user/0/net.yura.domination/files/assetpacks".equals(message)) {
                        return true;
                    }
                    if (message != null && (
                            message.startsWith("remove failed: ENOENT (No such file or directory) : /data/data/net.yura.domination/files/.java/.userPrefs/net/yura/domination/mobile/flashgui/prefs-") || // then some random GUID
                            message.startsWith("remove failed: ENOENT (No such file or directory) : /data/user/0/net.yura.domination/files/.java/.userPrefs/net/yura/domination/mobile/flashgui/prefs-"))) { // then some random GUID
                        return true;
                    }

                    return false;
                }
            } );

        }
        catch (Throwable th) {
            System.out.println("Grasshopper not loaded");
            RiskUtil.printStackTrace(th);
        }

        J2SELogger.setupLogging();

        if ( "true".equals( System.getProperty("debug") ) ) {

            // MWMWMWMWMWMWMWMWMWMWMWM ONLY DEBUG MWMWMMWMWMWMWMWMWMWMWMWMWM

            Logger.getLogger("").addHandler( new Handler() {
                boolean open;
                @Override
                public void publish(LogRecord record) {
                    if (record.getLevel().intValue() >= Level.WARNING.intValue()) {
                        if (!open) {
                            open = true;
                            try {
                                // TODO this does not work if the theme is not set yet, it will just throw an exception
                                OptionPane.showMessageDialog(null, record.getMessage()+" "+record.getThrown(), "WARN", OptionPane.WARNING_MESSAGE);
                            }
                            catch(Exception ex) {
                                RiskUtil.printStackTrace(ex);
                            }
                        }
                    }
                }

                @Override public void flush() { }
                @Override public void close() { }
            } );

            // cant do this on J2SE, swing will print too much junk.
            if (Application.getPlatform() != Application.PLATFORM_ME4SE) {
                // if we want to see DEBUG, default is INFO
                Logger.getLogger("").setLevel(java.util.logging.Level.ALL);
            }

            // so we do not need to wait for AI while testing
            net.yura.domination.engine.ai.AIManager.setWait(5);

            // MWMWMWMWMWMWMWMWMWMWM END ONLY DEBUG MWMWMMWMWMWMWMWMWMWMWMWM
        }

        if (appPreferences != null) {
            AIManager.setWait( appPreferences.getInt("ai_wait", AIManager.getWait()) );
            String lang = appPreferences.get("lang", null);
            if (lang!=null) {
                TranslationBundle.setLanguage(lang);
            }
            Risk.setShowDice(appPreferences.getBoolean(SHOW_DICE_KEY, DEFAULT_SHOW_DICE));
        }
        else {
            System.out.println("can not load appPreferences as it is NULL!");
        }
    }

/*
    @Override
    protected void destroyApp(boolean arg0) throws javax.microedition.midlet.MIDletStateChangeException {

        if (risk.getGame()!=null) {
            risk.parser("savegame auto.save");
        }
        risk.kill();
        try { risk.join(); } catch (InterruptedException e) { } // wait for game thread to die 

        super.destroyApp(arg0);
    }
*/

    @Override
    public void initialize(DesktopPane rootpane) {

        SynthLookAndFeel synth = null;

        try {
            if (Application.getPlatform() == Application.PLATFORM_ANDROID) {
                synth = (SynthLookAndFeel) Class.forName("net.yura.android.plaf.AndroidLookAndFeel").newInstance();

                // small hack to center radiobutton icon (the default height is too big, we set it to the width so the icon is square)
                Style radioButtonStyle = synth.getStyle("RadioButton");
                Icon radioButtonIcon = (Icon) radioButtonStyle.getProperty("icon", Style.ALL);
                if (radioButtonIcon != null) {
                    radioButtonStyle.addProperty(new CentreIcon(radioButtonIcon, radioButtonIcon.getIconWidth(), radioButtonIcon.getIconWidth()), "icon", Style.ALL);
                }
            }
            if (Application.getPlatform() == Application.PLATFORM_IOS) {
                synth = (SynthLookAndFeel) Class.forName("net.yura.ios.plaf.IOSLookAndFeel").newInstance();
            }
        }
        catch (Exception ex) {
            logger.log(Level.WARNING, "can not load theme", ex);
        }

        if (synth == null) {
            synth = new NimbusLookAndFeel();
        }

        InputStream themeData = Application.getResourceAsStream("/dom_synth.xml");
        try {
            synth.load(themeData);
        }
        catch (Exception ex) {
            throw new RuntimeException(ex);
        }
        finally {
            RiskUtil.close(themeData);
        }

        rootpane.setLookAndFeel( synth );

        MapChooser.loadThemeExtension(); // this has theme elements used inside AND outside of the MapChooser



        risk = new Risk();
        adapter = new MiniFlashRiskAdapter(risk);


        // this needs to run in the UI thread, otherwise 1 thread could be trying to read the auto.save file
        // and another trying to delete it, so we do all actions on the file in the same (UI) thread
        DesktopPane.invokeLater(new Runnable() {
            @Override
            public void run() {
                File autoSaveFile = getAutoSaveFile();
                if (autoSaveFile.exists()) {
                    logger.info("Loading from autosave");
                    // rename the file before we load it with the game thread so it does not get deleted by another thread
                    RiskUtil.rename(autoSaveFile, new File(autoSaveFile.getParent(),autoSaveFile.getName()+".load"));
                    risk.parser( "loadgame "+getAutoSaveFile()+".load" );
                }
                else {
                    adapter.openMainMenu();

                    if (hasPendingOpenLobby()) {
                        adapter.openLobby();
                    }
                }

                logger.info("UI STARTED");
            }
        });


        new Thread("Update-Version-Check") {
            @Override
            public void run() {

                // TODO check game version for non-PlayStore game
                //RiskUtil.getNewVersionCheck() is not good enough for android as uses RiskUtil.RISK_VERSION

                MapUpdateService.getInstance().init( MiniUtil.getFileList("map"), MapChooser.MAP_PAGE );
            }
        }.start();

        //risk.parser("newgame");
        //risk.parser("newplayer ai hard blue bob");
        //risk.parser("newplayer ai hard red fred");
        //risk.parser("newplayer ai hard green greg");
        //risk.parser("startgame domination increasing");

//        try {
//            File saves = new File( net.yura.android.AndroidMeApp.getIntance().getFilesDir() ,"saves");
//            File sdsaves = new File("/sdcard/Domination-saves");
//            copyFolder(saves, sdsaves);
//            copyFolder(sdsaves, saves);
//            System.out.println("files"+ Arrays.asList( saves.list() ) );
//        }
//        catch (Exception ex) {
//            RiskUtil.printStackTrace(ex);
//        }
    }

    public static void quit() {
        // HACK: if the user hits quit 2 times in a row,
        // the 2nd event may throw a nullpointer as desktopPane is set to null after the 1st
        if (net.yura.mobile.gui.DesktopPane.getDesktopPane() != null) {

            logger.info("UI QUIT");

            Application.exit();
        }
    }

    public static class CentreIcon extends Icon {
        Icon wrappedIcon;
        public CentreIcon(Icon icon,int w,int h) {
            wrappedIcon = icon;
            width = w;
            height = h;
        }
        @Override
        public void paintIcon(Component c, Graphics2D g, int x, int y) {
            // paint real icon in the middle of this icon
            wrappedIcon.paintIcon(c, g, x + (getIconWidth()-wrappedIcon.getIconWidth())/2, y + (getIconHeight()-wrappedIcon.getIconHeight())/2);
        }
    }

    public static boolean getBoolean(String key, boolean deflt) {
        if (appPreferences == null) return deflt;
        return appPreferences.getBoolean(key, deflt);
    }

    public static String getString(String key, String defaultValue) {
        if (appPreferences == null) return defaultValue;
        return appPreferences.get(key, defaultValue);
    }

    public static void saveGameSettings(String gameTypeCommand, String cardTypeCommand, boolean autoPlaceAllBoolean, boolean recycleCardsBoolean) {
        if (appPreferences != null) {
            appPreferences.put(DEFAULT_GAME_TYPE_KEY, gameTypeCommand);
            appPreferences.put(DEFAULT_CARD_TYPE_KEY, cardTypeCommand);
            appPreferences.putBoolean(DEFAULT_AUTO_PLACE_ALL_KEY, autoPlaceAllBoolean);
            appPreferences.putBoolean(DEFAULT_RECYCLE_CARDS_KEY, recycleCardsBoolean);
            flushPreferences();
        }
    }

    public static void setAccounts(List<String> accounts) {
        if (!accounts.isEmpty()) {
            if (appPreferences != null) {
                appPreferences.put("accounts", MiniUtil.listToCsv(accounts, ','));
                flushPreferences();
            }
        }
    }

    public static String getAccountsString() {
        String accounts = getString("accounts", null);
        // if we accidentally saved an empty string in an old version, remove it
        if ("".equals(accounts)) {
            appPreferences.remove("accounts");
            flushPreferences();
            return null;
        }
        return accounts;
    }

    private static void flushPreferences() {
        try {
            appPreferences.flush();
        }
        catch(Exception ex) {
            logger.log(Level.WARNING, "can not flush prefs", ex);
        }
    }

    public void setGooglePlayGameServices(GooglePlayGameServices listener) {
	googlePlayGameServices = listener;
    }
    public static GooglePlayGameServices getGooglePlayGameServices() {
	DominationMain main = (DominationMain) Application.getInstance();
        // main is only null if the app is in the process of shutting down.
	return main == null ? null : main.googlePlayGameServices;
    }

    // ----------------------------- calling native Activity -----------------------------

    private static Map<Integer,ActivityResultListener> nativeCalls = new HashMap();
    private static int nativeCallsCount = 100000; // auto Ids need to start higher then all hard coded ids.

    public interface ActivityResultListener {
        void onActivityResult(Object data);
        void onCanceled();
    }

    public static void openURL(String url, ActivityResultListener listener) {
        nativeCallsCount++;
        url = url + (url.indexOf('?') >= 0 ? "&" : "?") + "requestCode=" + nativeCallsCount;
        nativeCalls.put(nativeCallsCount,listener);
        Application.openURL(url);
    }

    public void onResult(int requestCode, int resultCode, Object obj) {
        ActivityResultListener listener = nativeCalls.remove(requestCode);
        if (listener != null) {
            if (resultCode == -1) { // Activity.RESULT_OK
                listener.onActivityResult(obj);
            }
            else if (resultCode == 0) { // Activity.RESULT_CANCELED
                listener.onCanceled();
            }
            else {
                logger.warning("unknown resultCode "+resultCode);
            }
        }
    }

    // ----------------------------- handle open from notification -----------------------------

    private Game pendingOpenGame;

    public boolean hasPendingOpenLobby() {
        return pendingOpenGame != null;
    }

    public void lobbyConnected() {
        if (pendingOpenGame != null) {
            adapter.lobby.playGame(pendingOpenGame);
            pendingOpenGame = null;
        }
    }

    public void pushNotificationsToken(String token) {

        if (Application.getPlatform() == Application.PLATFORM_IOS) {

            String apsEnvironment = System.getProperty("aps-environment");

            logger.info("Apple Push Token " + apsEnvironment + " " + token);

            // if this is a dev build, this token will ONLY work on apples sandbox push server
            if ("development".equals(apsEnvironment)) {
                token = "sandbox-" + token;
            }

            // we only request the token once we have connected
            MiniLobbyClient lobby = adapter.lobby;
            // if the user has closed the lobby by the time we get the token we have nothing we can do
            if (lobby != null) {
                lobby.mycom.setPushToken(PushLobbyClient.PUSH_SYSTEM_APN, token);
            }
        }
    }

    public void openNotification(Map params) {

        String gameId = (String)params.get(PushLobbyClient.GAME_ID);
        String options = (String)params.get(PushLobbyClient.OPTIONS);

        if (gameId != null) {
            Game game = new Game();
            game.setId(Integer.parseInt(gameId));
            game.setOptions(options);

            MiniFlashRiskAdapter ui = adapter;
            if (ui != null) {
                if (ui.lobby != null) {
                    if (ui.lobby.whoAmI() != null) {
                        ui.lobby.playGame(game);
                    }
                    else {
                        pendingOpenGame = game;
                        logger.warning("lobby open but we are not logged in yet");
                    }
                }
                else {
                    pendingOpenGame = game;
                    ui.openLobby();
                }
            }
            else {
                // the game has not initialized yet
                pendingOpenGame = game;
            }
        }
        else {
            logger.info("opened from notification, but no game info " + params);
        }
    }

    // ----------------------------- GAME SAVE -----------------------------

    private final static String AUTO_SAVE_FILE_NAME = "auto.save";
    public static File getAutoSaveFile() {
        return new File(MiniUtil.getSaveGameDir(), AUTO_SAVE_FILE_NAME);
    }

    public boolean shouldSaveGame() {
        Risk risk = this.risk;
        return risk != null && risk.getGame() != null && risk.getLocalGame();
    }

    /**
     * this is called when the user decides to quit the game, in that situation saveState will NOT be called
     * this is also called when a transparent activity is opened over the game, (e.g. GamePreferenceActivity)
     * in that case, we do not want to waste time saving state, as we know we will not get removed.
     */
    protected void pauseApp() {
        super.pauseApp();

        logger.info("[GameActivity] onPause");
        // if everything is shut down and there is no current game
        // make sure we clean up so no game is loaded on next start

        // TODO we may have been paused WHILE the game is starting,
        // and then we may end up deleting the file we are trying to load.
        if ( !shouldSaveGame() ) {
            File file = getAutoSaveFile();
            if (file.exists()) {
                logger.info("[GameActivity] DELETING AUTOSAVE");
                file.delete();
            }
        }
    }

    public void saveState() {
        logger.info("[GameActivity] onSaveInstanceState");
        // if the system wants to kill our activity we need to save the game if we have one

        if (shouldSaveGame()) {
            logger.info("[GameActivity] SAVING TO AUTOSAVE");
            // in game thread, we do not want to do it there as we will not know when its finished
            //getRisk().parser("savegame "+getAutoSaveFileURL());

            try {
                final Risk risk = this.risk;
                if (risk != null) {
                    final File autoSaveFile = DominationMain.getAutoSaveFile();
                    final File tempSaveFile = new File(autoSaveFile.getParent(), autoSaveFile.getName() + ".part");

                    risk.parserAndWait("savegame " + DominationMain.getAutoSaveFile() + ".part");
                    // if we may have closed the game while also closing the activity
                    // the save probably failed, and the rename will fail for sure.
                    if (shouldSaveGame()) {
                        RiskUtil.rename(tempSaveFile, autoSaveFile);
                    }
                }
            }
            catch (Exception ex) {
                logger.log(Level.WARNING, "onSaveInstanceState AUTOSAVE Error", ex);
            }
        }
    }
}
