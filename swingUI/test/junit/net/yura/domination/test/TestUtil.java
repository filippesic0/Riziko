package net.yura.domination.test;

import java.io.File;
import net.yura.domination.engine.Risk;
import net.yura.domination.engine.ai.AIManager;
import net.yura.domination.engine.core.RiskGame;
import net.yura.domination.guishared.RiskFileFilter;
import net.yura.domination.guishared.RiskUIUtil;

public class TestUtil {

    public static void setupMapsForTest() throws Exception {
            // we must set the maps folder for map loading to work
            RiskUIUtil.mapsdir = new File("maps").toURI().toURL();
    }

    public static Risk newRisk() throws Exception {
        setupMapsForTest();

        // this may or may not reload the ai wait time from game.ini file
        Risk risk = new Risk();

        // we want test to run quickly
        AIManager.setWait(0);
        Risk.setShowDice(false);

        return risk;
    }

    public static RiskGame newRiskGame() throws Exception {
        setupMapsForTest();

        return new RiskGame();
    }

    public static File getScriptFile(String mode) {
        File resFolder = new File("../../../res/test_scripts");
        return new File(resFolder, mode.replace(' ', '-') + "." + RiskFileFilter.RISK_SCRIPT_FILES);
    }
}
