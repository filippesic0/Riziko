// Yura Mamyrin, Group D

package net.yura.domination.ui.swinggui;

import java.awt.Toolkit;
import javax.swing.JFrame;
import javax.swing.SwingUtilities;
import net.yura.domination.engine.Risk;
import net.yura.domination.guishared.RiskUIUtil;
import net.yura.domination.guishared.AboutDialog;

/**
 * <p> Swing GUI Main Frame </p>
 * @author Yura Mamyrin
 */
public class SwingGUIFrame {

	public static void main(final String[] argv) {
		RiskUIUtil.parseArgs(argv);

                final Risk r = new Risk();
		SwingGUIPanel sg = new SwingGUIPanel( r );

		final JFrame gui = new JFrame();

		gui.setContentPane( sg );
                gui.setJMenuBar( sg.getJMenuBar() );
		gui.setTitle( SwingGUIPanel.product );
		gui.setIconImage(Toolkit.getDefaultToolkit().getImage( AboutDialog.class.getResource("icon.gif") ));
                gui.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);

                SwingUtilities.invokeLater(new Runnable() {
                    public void run() {

                        // we HAVE to run pack() from UI thread or we get a deadlock on jdk1.8 Ubuntu20.04.1
                        // because pack() first takes the AWTTreeLock then calls ... JViewport.reshape
                        // that fires AtkWrapper.emitSignal(ac, AtkSignal.OBJECT_VISIBLE_DATA_CHANGED, null)
                        // that calls at org.GNOME.Accessibility.AtkUtil.invokeInSwing(AtkUtil.java:68)
                        // and tells a component to revalidate that tries to get the AWTTreeLock again
                        gui.pack();

                        RiskUIUtil.center(gui);
                        RiskUIUtil.setMinimumSize(gui, gui.getPreferredSize());

                        gui.setVisible(true);

                        RiskUIUtil.openFile(argv,r);
                    }
                });

                // use main thread to check for map updates
		//sg.checkForUpdates();
	}
}
