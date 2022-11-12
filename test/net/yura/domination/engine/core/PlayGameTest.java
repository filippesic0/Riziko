package net.yura.domination.engine.core;

import java.io.File;
import junit.framework.TestCase;
import net.yura.domination.engine.Risk;
import net.yura.domination.engine.RiskAdapter;
import net.yura.domination.test.TestUtil;

public class PlayGameTest extends TestCase {
    
    public void testDominationFixedGames() throws Exception {
        playGame(Risk.STARTGAME_OPTION_MODE_DOMINATION + " fixed recycle");
    }
    public void testDominationIncreasingGames() throws Exception {
        playGame(Risk.STARTGAME_OPTION_MODE_DOMINATION + " increasing recycle");
    }
    public void testDominationItalianGames() throws Exception {
        playGame(Risk.STARTGAME_OPTION_MODE_DOMINATION + " italianlike recycle");
    }


    public void testCapitalFixedGames() throws Exception {
        playGame(Risk.STARTGAME_OPTION_MODE_CAPITAL + " fixed recycle");
    }
    public void testCapitalIncreasingGames() throws Exception {
        playGame(Risk.STARTGAME_OPTION_MODE_CAPITAL + " increasing recycle");
    }
    public void testCapitalItalianGames() throws Exception {
        playGame(Risk.STARTGAME_OPTION_MODE_CAPITAL + " italianlike recycle");
    }


    public void testMissionFixedGames() throws Exception {
        playGame(Risk.STARTGAME_OPTION_MODE_SECRET_MISSION + " fixed recycle");
    }
    public void testMissionIncreasingGames() throws Exception {
        playGame(Risk.STARTGAME_OPTION_MODE_SECRET_MISSION + " increasing recycle");
    }
    public void testMissionItalianGames() throws Exception {
        playGame(Risk.STARTGAME_OPTION_MODE_SECRET_MISSION + " italianlike recycle");
    }

    public void playGame(String mode) throws Exception {
        File file = TestUtil.getScriptFile(mode);
        
        playGame(file);
    }
    
    public void playGame(File file) throws Exception {
        //InputStream in = ReplayGameTest.class.getResourceAsStream("test.risk");
        Risk risk = TestUtil.newRisk();

        risk.addRiskListener(new RiskAdapter() {
            public void sendMessage(String output, boolean redrawNeeded, boolean repaintNeeded) {
                //System.out.println(output);
            }

            /**
             * if the game finishes or the replay thread fails, it will call here
             */
            public void needInput(int s) {
                //System.out.println("need input " + s);
                synchronized (risk) {
                    risk.notifyAll();
                }
            }
        });

        risk.parserAndWait("newgame");
        risk.parserAndWait("play " + file.getPath()); // maybe getAbsolutePath() for full path

        // keep waiting untill we have a running game
        while (risk.getGame() == null || risk.getGame().getState() == RiskGame.STATE_NEW_GAME) {
            synchronized (risk) {
                risk.wait();
            }
        }
            
        assertEquals(RiskGame.STATE_GAME_OVER, risk.getGame().getState());
                    
        System.out.println("winner " + risk.getGame().getCurrentPlayer());
        risk.parserAndWait("closegame");
        risk.kill();
    }
}
