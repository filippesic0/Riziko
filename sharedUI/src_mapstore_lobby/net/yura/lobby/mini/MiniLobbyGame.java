package net.yura.lobby.mini;

import java.util.Collection;
import net.yura.lobby.model.Game;
import net.yura.lobby.model.GameType;
import net.yura.lobby.model.Player;
import net.yura.mobile.gui.Icon;
import net.yura.mobile.util.Properties;

/**
 * A simpler interface then LobbyGame that only allows 1 open game at a time.
 * @see net.yura.lobby.client.LobbyGame
 * @author Yura Mamyrin
 */
public interface MiniLobbyGame {

    void addLobbyGameMoveListener(MiniLobbyClient lgl);

    Properties getProperties();
    void openChat();

    boolean isMyGameType(GameType gametype);
    Icon getIconForGame(Game game);
    String getGameDescription(Game game);

    /**
     * callback mlc.createNewGame(Game)
     */
    void openGameSetup(GameType gameType);

    /**
     * this method must trigger mlc.mycom.playGame(game.getId()) at some point in the future
     */
    void prepareAndOpenGame(Game game);

    void objectForGame(Object object);
    void stringForGame(String message);

    void connected(String username);
    void disconnected();

    /**
     * button inside lobby was clicked that the user wants to join a private game
     */
    void loginGoogle();
    /**
     * a private game was started on the server
     */
    void gameStarted(int id);

    String getAppName();
    String getAppVersion();

    void lobbyShutdown();

    void showMessage(String fromwho, String message);

    void addSpectator(Player player);
    void removeSpectator(String player);
    void renameSpectator(String oldname, String newname, int newtype);

    void updatePlayerList(Collection<Player> playersInGame, String whoTurn);
}
