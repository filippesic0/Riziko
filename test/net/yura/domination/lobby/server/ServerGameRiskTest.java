package net.yura.domination.lobby.server;

import junit.framework.TestCase;

public class ServerGameRiskTest extends TestCase {
    
    public ServerGameRiskTest(String testName) {
        super(testName);
    }
    
    @Override
    protected void setUp() throws Exception {
        super.setUp();
    }
    
    @Override
    protected void tearDown() throws Exception {
        super.tearDown();
    }

    /**
     * Test of compare method, of class ServerGameRisk.
     */
    public void testCompareVersions() {
        System.out.println("test ServerGameRisk.compare");

        assertEquals(0, ServerGameRisk.compare(new int[] {1,2,3}, new int[] {1,2,3}));

        assertEquals(-1, ServerGameRisk.compare(new int[] {0,0,0}, new int[] {1,2,3}));
        assertEquals(-1, ServerGameRisk.compare(new int[] {5,5,5}, new int[] {5,5,6}));
        assertEquals(-1, ServerGameRisk.compare(new int[] {1,1,1,7}, new int[] {1,2,0}));
        assertEquals(-1, ServerGameRisk.compare(new int[] {1,1,9}, new int[] {1,2,1}));
        
        assertEquals(1, ServerGameRisk.compare(new int[] {1,2,3}, new int[] {1,1,1}));
        assertEquals(1, ServerGameRisk.compare(new int[] {5,5,6}, new int[] {5,5,5}));
        assertEquals(1, ServerGameRisk.compare(new int[] {1,2,1}, new int[] {1,1,9}));
    }
}
