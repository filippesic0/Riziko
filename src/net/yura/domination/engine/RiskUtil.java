package net.yura.domination.engine;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.Closeable;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.io.PrintWriter;
import java.io.PushbackInputStream;
import java.net.URL;
import java.nio.charset.Charset;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Properties;
import java.util.ResourceBundle;
import java.util.StringTokenizer;
import java.util.logging.Level;
import java.util.logging.Logger;
import java.util.prefs.Preferences;
import net.yura.domination.engine.core.Player;
import net.yura.domination.engine.core.RiskGame;
import net.yura.domination.engine.translation.MapTranslator;

public class RiskUtil {

        public static final Object SUCCESS = "SUCCESS";
        public static final Object ERROR = "ERROR";

	public static final String RISK_VERSION_URL;
	public static final String RISK_LOBBY_URL;
//	public static final String RISK_POST_URL; // look in Grasshopper.jar now
	public static final String GAME_NAME;
	public static final String RISK_VERSION;
//	private static final String DEFAULT_MAP;

        private static boolean oldVersion;

        private static final Logger logger = Logger.getLogger(RiskUtil.class.getName());
	public static RiskIO streamOpener;

        /**
         * @see java.nio.charset.StandardCharsets#UTF_8
         */
        public final static Charset UTF_8 = Charset.forName("UTF-8");
        
	static {

		Properties settings = new Properties();

		InputStream settingsData = RiskUtil.class.getResourceAsStream("settings.ini");
		try {
			settings.load(settingsData);
		}
		catch (Exception ex) {
			throw new RuntimeException("can not find settings.ini file!",ex);
		}
		finally {
		    close(settingsData);
		}

		RISK_VERSION_URL = settings.getProperty("VERSION_URL");
		RISK_LOBBY_URL = settings.getProperty("LOBBY_URL");
//		RISK_POST_URL = settings.getProperty("POST_URL");
		GAME_NAME = settings.getProperty("name");
		//DEFAULT_MAP = settings.getProperty("defaultmap");
		RISK_VERSION = settings.getProperty("version");

		String dmap = settings.getProperty("defaultmap");
		String dcards = settings.getProperty("defaultcards");

		RiskGame.setDefaultMapAndCards( dmap , dcards );
	}

	public static void close(Closeable obj) {
	    try {
	        if (obj != null) {
                obj.close();
            }
        }
        catch (Exception ex) {
            logger.info("not able to close " + obj);
        }
    }

	public static InputStream openMapStream(String a) throws IOException {
            if (a == null) {
                throw new NullPointerException("map filename is null");
            }
            return streamOpener.openMapStream(a);
	}

	public static InputStream openStream(String a) throws IOException {
            return streamOpener.openStream(a);
	}

	public static ResourceBundle getResourceBundle(Class c,String n,Locale l) {
            return streamOpener.getResourceBundle(c, n, l);
	}

	public static void openURL(URL url) throws Exception {
            streamOpener.openURL(url);
	}

	public static void openDocs(String docs) throws Exception {
            streamOpener.openDocs(docs);
	}
        public static void saveFile(String file, RiskGame aThis) throws Exception {
            streamOpener.saveGameFile(file, aThis);
        }
        public static InputStream getLoadFileInputStream(String file) throws Exception {
            return streamOpener.loadGameFile(file);
        }

        public static void printStackTrace(Throwable ex) {
            logger.log(Level.WARNING, null, ex);
        }

        public static void donate() throws Exception {
		openURL(new URL("http://domination.sourceforge.net/donate.shtml"));
	}
        
	public static void donatePayPal() throws Exception {
		openURL(new URL("https://www.paypal.com/cgi-bin/webscr?cmd=_donations&business=yura%40yura%2enet&item_name="+GAME_NAME+"%20Donation&no_shipping=0&no_note=1&tax=0&currency_code=GBP&lc=GB&bn=PP%2dDonationsBF&charset=UTF%2d8"));
	}

        public static Properties getPlayerSettings(final Risk risk,Class uiclass) {
            Preferences prefs=null;
            try {
                 prefs = Preferences.userNodeForPackage( uiclass );
            }
            catch(Throwable th) { } // security
            final Preferences theprefs = prefs;
            return new Properties() {
                public String getProperty(String key) {
                    String value = risk.getRiskConfig(key);
                    if (theprefs!=null) {
                        value = theprefs.get(key, value);
                    }
                    return value;
                }                
            };
        }

        public static void loadPlayers(Risk risk,Class uiclass) {
            Properties playerSettings = getPlayerSettings(risk, uiclass);
            for (int cc=1;cc<=RiskGame.MAX_PLAYERS;cc++) {
                String name = playerSettings.getProperty("default.player"+cc+".name");
                String color = playerSettings.getProperty("default.player"+cc+".color");
                String type = playerSettings.getProperty("default.player"+cc+".type");
                if (name != null && color != null && type != null && !"".equals(name) && !"".equals(color) && !"".equals(type)) {
                    risk.parser("newplayer " + type + " " + color + " " + name);
                }
            }
        }

        public static void savePlayers(Risk risk,Class uiclass) {

            Preferences prefs=null;
            try {
                 prefs = Preferences.userNodeForPackage( uiclass );
            }
            catch(Throwable th) { } // security

            if (prefs!=null) {

                List players = risk.getGame().getPlayers();

                for (int cc=1;cc<=RiskGame.MAX_PLAYERS;cc++) {
                    String nameKey = "default.player"+cc+".name";
                    String colorKey = "default.player"+cc+".color";
                    String typeKey = "default.player"+cc+".type";

                    String name = "";
                    String color = "";
                    String type = "";

                    Player player = (cc<=players.size())?(Player)players.get(cc-1):null;

                    if (player!=null) {
                        name = player.getName();
                        color = ColorUtil.getStringForColor( player.getColor() );
                        type = risk.getType( player.getType() );
                    }
                    prefs.put(nameKey, name);
                    prefs.put(colorKey, color);
                    prefs.put(typeKey, type);

                }

                // on android this does not work, god knows why
                // whats the point of including a class if its
                // most simple and basic operation does not work?
                try {
                    prefs.flush();
                }
                catch(Exception ex) {
                    logger.log(Level.INFO, "can not flush prefs", ex);
                }

            }
        }

        public static void savePlayers(List players,Class uiclass) {

            Preferences prefs=null;
            try {
                 prefs = Preferences.userNodeForPackage( uiclass );
            }
            catch(Throwable th) { } // security

            if (prefs!=null) {

                for (int cc=1;cc<=RiskGame.MAX_PLAYERS;cc++) {
                    String nameKey = "default.player"+cc+".name";
                    String colorKey = "default.player"+cc+".color";
                    String typeKey = "default.player"+cc+".type";

                    String name = "";
                    String color = "";
                    String type = "";
                    
                    String[] player = (cc<=players.size())?(String[])players.get(cc-1):null;

                    if (player!=null) {
                        name = player[0];
                        color = player[1];
                        type = player[2];
                    }
                    prefs.put(nameKey, name);
                    prefs.put(colorKey, color);
                    prefs.put(typeKey, type);

                }

                // on android this does not work, god knows why
                // whats the point of including a class if its
                // most simple and basic operation does not work?
                try {
                    prefs.flush();
                }
                catch(Exception ex) {
                    logger.log(Level.INFO, "can not flush prefs", ex);
                }

            }
        }
        
        public static BufferedReader readMap(InputStream in) throws IOException {

            PushbackInputStream pushback = new PushbackInputStream(in,3);

            int first = pushback.read();
            if (first == 0xEF) {
                int second = pushback.read();
                if (second == 0xBB) {
                    int third = pushback.read();
                    if (third == 0xBF) {
                        return new BufferedReader(new InputStreamReader( pushback, "UTF-8" ) );
                    }
                    pushback.unread(third);
                }
                pushback.unread(second);
            }
            pushback.unread(first);

            return new BufferedReader(new InputStreamReader( pushback, "ISO-8859-1" ) );
        }

        /**
         * gets the info for a map or cards file
         * in the case of map files it will get the "name" "crd" "prv" "pic" "map" and any "comment" and number of "countries"
         * and for cards it will have a "missions" that will contain the String[] of all the missions
         */
	public static Map loadInfo(String fileName, boolean cards) {

            Map info = new HashMap();

            for (int c=0;true;c++) {

                BufferedReader bufferin=null;

                try {

                        bufferin = RiskUtil.readMap(RiskUtil.openMapStream(fileName));
                        List misss = null;
                        MapTranslator mapTranslator = null;

                        if (cards) {
                            mapTranslator = new MapTranslator();
                            mapTranslator.setCards(fileName);
                            misss = new ArrayList();
                        }

                        String input = bufferin.readLine();
                        String mode = null;

                        while(input != null) {

                                if (input.equals("")) {
                                        // do nothing
                                        //System.out.print("Nothing\n"); // testing
                                }
                                else if (input.charAt(0)==';') {
                                    String comment = (String)info.get("comment");
                                    String com = input.substring(1).trim();
                                    if (comment==null) {
                                        comment = com;
                                    }
                                    else {
                                        comment = comment +"\n"+com;
                                    }
                                    info.put("comment", comment);
                                }
                                else {

                                        if (input.charAt(0)=='[' && input.charAt( input.length()-1 )==']') {
                                                mode="newsection";
                                        }

                                        if ("files".equals(mode)) {

                                                int space = input.indexOf(' ');

                                                if (space < 0) {
                                                    throw new RuntimeException("invalid file " + input);
                                                }

                                                String fm = input.substring(0,space);
                                                String val = input.substring(space+1);

                                                info.put( fm , val);

                                        }
                                        else if ("borders".equals(mode)) {
                                                // we dont care about anything in or after the borders section
                                                break;
                                        }
                                        else if ("countries".equals(mode)) {
                                                int space = input.indexOf(' ');

                                                if (space < 0) {
                                                    throw new RuntimeException("invalid country " + input);
                                                }

                                                info.put("countries", Integer.parseInt(input.substring(0, space)));
                                        }
                                        else if ("missions".equals(mode)) {

                                                StringTokenizer st = new StringTokenizer(input);
                                            
                                                String description=mapTranslator.getTranslatedMissionName(st.nextToken()+"-"+st.nextToken()+"-"+st.nextToken()+"-"+st.nextToken()+"-"+st.nextToken()+"-"+st.nextToken());

                                                if (description==null) {

                                                        StringBuffer d = new StringBuffer();

                                                        while (st.hasMoreElements()) {

                                                                d.append( st.nextToken() );
                                                                d.append( " " );
                                                        }

                                                        description = d.toString();

                                                }

                                                misss.add( description );

                                        }
                                        else if ("newsection".equals(mode)) {

                                                mode = input.substring(1, input.length()-1); // set mode to the name of the section

                                        }
                                        else if (mode == null) {
                                            if (input.indexOf(' ')>0) {
                                                info.put( input.substring(0,input.indexOf(' ')) , input.substring(input.indexOf(' ')+1) );
                                            }
                                        }
                                        // if "continents" or "cards" then just dont do anything in those sections

                                }

                                input = bufferin.readLine(); // get next line
                        }

                        if (cards) {
                            info.put("missions", (String[])misss.toArray(new String[misss.size()]) );
                            misss = null;
                        }

                        break;
                }
                catch(IOException ex) {
                        System.err.println("Error trying to load: "+fileName);
                        RiskUtil.printStackTrace(ex);
                        if (c < 5) { // retry
                                try { Thread.sleep(1000); } catch(Exception ex2) { }
                        }
                        else { // give up
                                break;
                        }
                }
                catch (RuntimeException ex) {
                    System.err.println("Error trying to load: " + fileName);
                    throw ex;
                }
                finally {
                    if (bufferin!=null) {
                        try { bufferin.close(); } catch(Exception ex2) { }
                    }
                }
            }

            return info;
	}
        
        /**
         * This is only non empty when loading from random file locations in the MapEditor
         */
        public static String getContext(String f) {
                int slash = f.lastIndexOf('\\');
                if (slash >= 0) {
                    return f.substring(0, slash + 1);
                }
                slash = f.lastIndexOf('/');
                if (slash >= 0) {
                    return f.substring(0, slash + 1);
                }
                return "";
        }

        public static void saveGameLog(File logFile, RiskGame game) throws IOException {
            FileWriter fileout = new FileWriter(logFile);
            BufferedWriter buffer = new BufferedWriter(fileout);
            PrintWriter printer = new PrintWriter(buffer);
            List commands = game.getCommands();
            int size = commands.size();
            for (int line = 0; line < size; line++) {
                printer.println(commands.get(line));
            }
            printer.close();
        }

        public static OutputStream getOutputStream(File dir,String fileName) throws Exception {
            File outFile = new File(dir,fileName);
            // as this could be dir=.../maps fileName=preview/file.jpg
            // we need to make sure the preview dir exists, and if it does not, we must make it
            File parent = outFile.getParentFile();
            if (!parent.isDirectory() && !parent.mkdirs()) { // if it does not exist and i cant make it
                throw new RuntimeException("can not create dir "+parent);
            }
            return new FileOutputStream( outFile );
        }

        public static void rename(File oldFile,File newFile) {
            if (newFile.exists() && !newFile.delete()) {
                throw new RuntimeException("can not del dest file: "+newFile);
            }
            if (!oldFile.renameTo(newFile)) {
                try {
                    copy(oldFile, newFile);
                    if (!oldFile.delete()) {
                        // this is not so bad, but still very strange
                        System.err.println("can not del source file: "+oldFile);
                    }
                }
                catch(Exception ex) {
                    throw new RuntimeException("rename failed: from: "+oldFile+" to: "+newFile,ex);
                }
            }
        }

        /**
         * this method must NEVER throw an exception, even if everything goes very very wrong
         */
        public static String getNewVersionCheck() {
            try {
                URL url = new URL(RiskUtil.RISK_VERSION_URL);

                BufferedReader bufferin=new BufferedReader( new InputStreamReader(url.openStream()) );
                List buffer = new ArrayList();
                String input = bufferin.readLine();

                while(input != null) {
                        buffer.add(input);
                        input = bufferin.readLine(); // get next line
                }

                String[] newversion = (String[])buffer.toArray( new String[buffer.size()] );
                
                if (newversion[0].startsWith("RISKOK ")) {

                        String v = newversion[0].substring(7, newversion[0].length() );

                        if (!v.equals(RiskUtil.RISK_VERSION)) {
                                oldVersion = true;

                                for (int c=1;c<newversion.length;c++) {
                                        v = v+"\n"+newversion[c];
                                }
                
                                return v;
                        }
                }
            }
            catch (Throwable e) {
                logger.info("version check fail " + e);
            }

            return null;
        }

    public static void setOldVersion() {
        oldVersion = true;
    }

    public static boolean isOldVersion() {
        return oldVersion;
    }

    public static java.util.Vector asVector(java.util.List list) {
        return list instanceof java.util.Vector?(java.util.Vector)list:new java.util.Vector(list);
    }

    public static java.util.Hashtable asHashtable(Map map) {
        return map instanceof java.util.Hashtable?(java.util.Hashtable)map:new java.util.Hashtable(map);
    }

    /**
     * TODO move this to use the java 1.5 method
     * @see String#replace(java.lang.CharSequence, java.lang.CharSequence) 
     */
    public static String replaceAll(String string, String notregex, String replacement) {
        return string.replaceAll( quote(notregex) , quoteReplacement(replacement));
    }

    /**
     * @see java.util.regex.Pattern#quote(java.lang.String)
     */
    public static String quote(String s) {
        int slashEIndex = s.indexOf("\\E");
        if (slashEIndex == -1)
            return "\\Q" + s + "\\E";

        StringBuilder sb = new StringBuilder(s.length() * 2);
        sb.append("\\Q");
        slashEIndex = 0;
        int current = 0;
        while ((slashEIndex = s.indexOf("\\E", current)) != -1) {
            sb.append(s.substring(current, slashEIndex));
            current = slashEIndex + 2;
            sb.append("\\E\\\\E\\Q");
        }
        sb.append(s.substring(current, s.length()));
        sb.append("\\E");
        return sb.toString();
    }

    /**
     * @see java.util.regex.Matcher#quoteReplacement(java.lang.String)
     */
    public static String quoteReplacement(String s) {
        if ((s.indexOf('\\') == -1) && (s.indexOf('$') == -1))
            return s;
        StringBuffer sb = new StringBuffer();
        for (int i=0; i<s.length(); i++) {
            char c = s.charAt(i);
            if (c == '\\') {
                sb.append('\\'); sb.append('\\');
            } else if (c == '$') {
                sb.append('\\'); sb.append('$');
            } else {
                sb.append(c);
            }
        }
        return sb.toString();
    }

    
    
    
    
    public static void copy(File src, File dest) throws IOException {
     
            if(src.isDirectory()){
     
                    //if directory not exists, create it
                    if(!dest.exists()){
                       dest.mkdir();
                       System.out.println("Directory copied from " 
                                  + src + "  to " + dest);
                    }
     
                    //list all the directory contents
                    String files[] = src.list();
     
                    for (int c=0;c<files.length;c++) {
                       //construct the src and dest file structure
                       File srcFile = new File(src, files[c]);
                       File destFile = new File(dest, files[c]);
                       //recursive copy
                       copy(srcFile,destFile);
                    }
     
            }else{
                    //if file, then copy it
                    //Use bytes stream to support all file types
                    InputStream in = new FileInputStream(src);
                    OutputStream out = new FileOutputStream(dest); 
     
                    byte[] buffer = new byte[1024];
     
                    int length;
                    //copy the file content in bytes 
                    while ((length = in.read(buffer)) > 0){
                       out.write(buffer, 0, length);
                    }
     
                    in.close();
                    out.close();
                    System.out.println("File copied from " + src + " to " + dest);
            }
    }

    public static String getAtLeastOne(StringTokenizer stringT) {
        StringBuilder text = new StringBuilder(stringT.nextToken());
        while ( stringT.hasMoreTokens() ) {
            text.append(' ');
            text.append(stringT.nextToken());
        }
        return text.toString();
    }

    /**
     * @see net.yura.domination.guishared.RiskFileFilter#getExtension(java.io.File)
     * @see net.yura.domination.tools.mapeditor.MapsTools#getExtension(java.io.File)
     */
    public static String getFileNameWithoutExtension(String filename) {
        int dotIndex = filename.lastIndexOf('.');
        // if file starts with a dot, this is a hidden file, not an extension
        return dotIndex > 0 ? filename.substring(0, dotIndex) : filename;
    }
}
