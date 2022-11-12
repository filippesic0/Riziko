//  Group D

package net.yura.domination.engine.ai.logic;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.PriorityQueue;
import java.util.Set;
import java.util.Stack;
import java.util.StringTokenizer;
import net.yura.domination.engine.Risk;
import net.yura.domination.engine.ai.AISubmissive;
import net.yura.domination.engine.core.Card;
import net.yura.domination.engine.core.Continent;
import net.yura.domination.engine.core.Country;
import net.yura.domination.engine.core.Player;
import net.yura.domination.engine.core.RiskGame;
import net.yura.domination.engine.core.StatType;
import net.yura.domination.engine.core.Statistic;

/**
 * @author Steven Hawkins
 *
 * TODO:
 * fear reprisals
 */
public class AIDomination extends AISubmissive {

	static final int MAX_AI_TURNS = 300;
	public static final int PLAYER_AI_TEST = 5;
	public static final int PLAYER_AI_AVERAGE = 4;
	public final static int PLAYER_AI_HARD = 2;
	public final static int PLAYER_AI_EASY = 1;
	    
        public int[] iminimap;
        public int[][] minimap;
        public static int indroll=0;
        public static double[] threats=new double[256];//pretnje bez racunanja same bitke
        public static double[] threats1=new double[256];//pretnje trenutnom igracu posle bitke
        public static int[] indthreats=new int[255];//i njihovi indeksi
        public static List<List<Double>> threats2=new ArrayList<>();//pretnje skoro svakoj teritoriji kad bi ih drzao trenutni igrac
        public static int[] I=new int[RiskGame.MAX_PLAYERS];//brojac za continentpriority i borderids
        public static int[] J=new int[RiskGame.MAX_PLAYERS];//brojac za countrypriority
        public static int[] K=new int[RiskGame.MAX_PLAYERS];
        public static HashSet<Country> multiattackers=new HashSet<>();
        public static HashSet<Country> onewayattacked=new HashSet<>();
        public static HashSet<Country> onewayattackers=new HashSet<>();
        //public static List<Country> edge=new ArrayList<>();
        public static List<Country> toattack=new ArrayList<>();
        public static List<Country> todefend=new ArrayList<>();
        public static List<Integer> attacktype=new ArrayList<>();//napadamo dok ne ostane toliko tenkova odbrani
        public static List<Integer> towinmove=new ArrayList<>();//negativan broj znaci da je u pitanju worsedefence
        public static List<Integer> towinstay=new ArrayList<>();//negativan broj znaci da je u pitanju worsedefence
        public static List<Country> tofortify1=new ArrayList<>();
        public static List<Integer> tofortify2=new ArrayList<>();
        public static List<List<Card>> totrade=new ArrayList<>();
        public static HashSet<Country> Borders=new HashSet<>();
        public static HashSet<Country> fulldefended=new HashSet<>();
        public static HashSet<Country> betterdefence=new HashSet<>();
        public static HashSet<Country> worsedefence=new HashSet<>();
        public static HashSet<Country> extendedworsedefence=new HashSet<>();
        public static HashSet<Country> betterdefence1=new HashSet<>();
        public static HashSet<Country> worsedefence1=new HashSet<>();
        public static List<Continent> almostconquered=new ArrayList<>();
        public static List<Player> almostconqueredP=new ArrayList<>();
        public static Player Defender;
        public static int Defence;
        public static List<Country> minattackers=new ArrayList<>();

    protected final int type;
	private boolean eliminating;
	private Continent breaking;

    public AIDomination(int type) {
        this.type = type;
    }
	
	public void CreateAlliance()
	{	
		int p=game.getPlayers().size();
		double[] reinforcements=new double[p];
		int[] indexes=new int[p];
		for(int i=0;i<p;i++)
		{   reinforcements[i]=getReinforcements((Player)(game.getPlayers()).get(i));
			indexes[i]=i;
		}
		for(int i=0;i<p-1;i++)
		{   double max=0;
			int indmax=0;
			for(int j=i+1;j<p;j++)
				if(reinforcements[j]>max)
				{   max=reinforcements[j];
					indmax=j;
				}
			if(max>reinforcements[i])
			{   int p1;
				double p2;
				p1=indexes[i];
				indexes[i]=indexes[indmax];
				indexes[indmax]=p1;
				p2=reinforcements[i];
				reinforcements[i]=reinforcements[indmax];
				reinforcements[indmax]=p2;
			}
		}
		game.alliance.clear();
		int sumarmies=0;
		int count=0;
		for(int i=p-1;i>=0;i--)
		{   Player player = (Player)game.getPlayers().get(indexes[i]);
			int armies=0;
			HashSet<Country> countries= new HashSet<>();
			countries.addAll(player.getTerritoriesOwned());
			for(Country country:countries)
				armies+=country.getArmies();
			if(reinforcements[i]*2<=reinforcements[0]*1||(p==3&&reinforcements[i]*3<=reinforcements[0]*2))
			{	if(!game.alliance.contains(player))
					game.alliance.add(player);
			}
			else//Racunamo samo za one koji nisu u alijansi.
			{	sumarmies+=armies;
				count++;
			}
		}
		sumarmies/=count;
		//ako trenutni igrac ima dovoljno tenkova na tabli, ne moze biti clan alijanse, nego treba da napreduje:
		int armies=0;
		HashSet<Country> countries= new HashSet<>();
		countries.addAll(cplayer.getTerritoriesOwned());
		for(Country country:countries)
			armies+=country.getArmies();
		if(armies>=sumarmies)
			game.alliance.remove(cplayer);

		int sum=0;
		for(int i=p-1;i>0;i--)
			if(game.alliance.contains((Player)game.getPlayers().get(indexes[i])))
				sum+=reinforcements[i];
		for(int i=p-1;i>=0;i--)
		{   if(reinforcements[1]<sum&&reinforcements[i]*3>=reinforcements[0]*2||(p==3&&reinforcements[i]*4<=reinforcements[0]*3))
			if(game.alliance.contains((Player)game.getPlayers().get(indexes[i])))
				game.alliance.remove((Player)(game.getPlayers()).get(indexes[i]));
		}
	}
	
	@Override
	public String getPlaceArmies() {
		int l=game.getContinents().length;
		int p=game.getPlayers().size();
		int konst=0;//manipulatorska konstanta za ulazak u drugi if
		CreateAlliance();
		if(game.smallmap==-1)//osim ovoga, sve ostale stvari koje se rade jednom
		{   int summ;
			game.sumofdistances=SumOfDistances();
			//formiranje alijansi; broj kompjutera u alijansi mora biti veci od ukupnog broja ljudi dok se ne poboljsaju performanse
			int averages=0;
			int humans=0;
			for(int i=0;i<game.getPlayers().size();i++)
			{   Player pplayer=(Player)game.getPlayers().get(i);
				if(pplayer.getType()==AIDomination.PLAYER_AI_AVERAGE)
					averages++;
				if(pplayer.getType()==Player.PLAYER_HUMAN)
					humans++;
			}
			game.numberofgoodplayers = averages + humans;
			//numberofgoodplayers=game.getPlayers().size();
			int a=game.getCountries().length/p;
			summ=(game.getCountries().length-a*p)/3*(a+1);
			summ+=((a+1)*p-game.getCountries().length)/3*a;
			Continent[] continents=game.getContinents();
			for(int i=0;i<game.getContinents().length;i++)
				if(continents[i].getTerritoriesContained().size()<3)
					summ+=continents[i].getArmyValue();
			if((double)summ/p<4.5)
				game.smallmap=1;
			else
			{   game.smallmap=0;
				game.numberofgoodplayers=15;
			}
			game.Smallmap=game.smallmap;
			Country[] countries = game.getCountries();
			// <editor-fold defaultstate="collapsed">
			//odredjivanje svih ivicnih teritorija:
			/*for(Country country:countries)
			{   int j,i,n,ind=1;
				List<Country> neighbours=new ArrayList<>();
				neighbours.addAll(country.getIncomingNeighbours());
				n=neighbours.size();
				if(n<2)
				{   edge.add(country);
					continue;
				}
				if(n==2)
				{   if(!neighbours.get(0).isNeighbours(neighbours.get(1)))
						edge.add(country);
					else if(!neighbours.get(1).isNeighbours(neighbours.get(0)))
						edge.add(country);
					continue;
				}
				List<Integer> backtracking=new ArrayList<>();
				backtracking.add(0);
				j=0;//duzina liste backtracking
				while(true)
				{   if(ind==1)
					{   ind=0;
						for(i=0;i<n;i++)
						{   if(!backtracking.contains(i)&&neighbours.get(backtracking.get(j)).isNeighbours(neighbours.get(i)))
							{   backtracking.add(i);
								j++;
								ind=1;
								break;
							}
						}
					}
					if(ind==0)
					{   i=backtracking.get(j);
						backtracking.remove(j);
						j--;
						if(backtracking.isEmpty())
							break;
						for(i++;i<n;i++)
						{   if(!backtracking.contains(i)&&neighbours.get(backtracking.get(j)).isNeighbours(neighbours.get(i)))
							{   backtracking.add(i);
								j++;
								ind=1;
								break;
							}
						}
					}
					if(backtracking.size()==n)
					{   ind=0;
						if(neighbours.get(backtracking.get(backtracking.get(j))).isNeighbours(neighbours.get(0)))
							ind=1;
						break;
					}
				}
				if(ind==0)
					edge.add(country);
			}*/
			// </editor-fold>
			game.Smallmap=0;
			//onewayattacked.clear();
			for(Country country:countries)
			{   List<Country> neighbours=new ArrayList<>();
				neighbours.addAll(country.getIncomingNeighbours());
				neighbours.removeAll(country.getNeighbours());
				if(!neighbours.isEmpty())
				{   onewayattacked.add(country);
					onewayattackers.addAll(neighbours);
				}
				else
					neighbours.clear();
			}
			//trazimo teritorije koje se granice jednosmerno sa puno teritorija
			countries=game.getCountries();
			for(Country country1:countries)
			{   if(country1.getNeighbours().size()-country1.getIncomingNeighbours().size()>5)
					multiattackers.add(country1);
			}
		}
	if (this.type ==AIDomination.PLAYER_AI_AVERAGE&&game.getCardMode()==RiskGame.CARD_ITALIANLIKE_SET/*&&smallmap==0*/&&game.NoEmptyCountries())
		if (game.indplacearmies+konst<p&&Risk.indfortify==0)
		{	// <editor-fold defaultstate="collapsed">
			/*  if (!game.NoEmptyCountries())
				if (game.getPlayers().size()==2&&false)//skloni false
				{   Continent[] continents=game.getContinents();
					int i,indMax=0,minterritories=260;
					double Max=0;
					for(i=0;i<continents.length;i++)
						//if continent has empty countries
						if(continents[i].playerown[0]+continents[i].playerown[1]+continents[i].playerown[2]+continents[i].playerown[3]+continents[i].playerown[4]+continents[i].playerown[5]<continents[i].getTerritoriesContained().size())
						{   //searching for maximum % of continent which own one player
							int max=continents[i].playerown[0];
							for(int j=1;j<game.getPlayers().size();j++)
								if (continents[i].playerown[j]>max)
									max=continents[i].playerown[j];
							if (continents[i].getTerritoriesContained().size()<max*2)
								if ((double)max/continents[i].getTerritoriesContained().size()>Max)
								{   Max=(double)max/continents[i].getTerritoriesContained().size();
									minterritories=continents[i].getTerritoriesContained().size();
									indMax=i;
								}
								else if ((double)max/continents[i].getTerritoriesContained().size()==Max)
									if (continents[i].getTerritoriesContained().size()<minterritories)
									{   Max=(double)max/continents[i].getTerritoriesContained().size();
										minterritories=continents[i].getTerritoriesContained().size();
										indMax=i;
									}
						}
					if(minterritories==260)
					{   double maxpercentofplayers=0;
						double maxpercenttotal=0;
						int minborders=260;
						int mincountries=260;
						int maxdisance=0;
						int sum;
						//searching for continent on which we want country
						for(i=0;i<continents.length;i++)
						{   int numberofborders=continents[i].getBorderCountries().size();
							int numberofcountries=continents[i].getTerritoriesContained().size();
							sum=continents[i].playerown[0]+continents[i].playerown[1]+continents[i].playerown[2]+continents[i].playerown[3]+continents[i].playerown[4]+continents[i].playerown[5];
							if(sum<numberofcountries)
							{   if((continents[i].playerown[game.getPlayers().indexOf(cplayer)]+1.0)/(sum+1-continents[i].playerown[game.getPlayers().indexOf(cplayer)])>maxpercentofplayers)
								{   maxpercentofplayers=(continents[i].playerown[game.getPlayers().indexOf(cplayer)]+1.0)/(sum+1-continents[i].playerown[game.getPlayers().indexOf(cplayer)]);
									maxpercenttotal=(continents[i].playerown[game.getPlayers().indexOf(cplayer)]+1.0)/numberofcountries;
									minborders=numberofborders;
									mincountries=numberofcountries;
									indMax=i;
								}
								else if(abs((continents[i].playerown[game.getPlayers().indexOf(cplayer)]+1.0)/(sum+1-continents[i].playerown[game.getPlayers().indexOf(cplayer)])-maxpercentofplayers)<0.0001)
								if((continents[i].playerown[game.getPlayers().indexOf(cplayer)]+1.0)/numberofcountries>maxpercenttotal)
								{   maxpercentofplayers=(continents[i].playerown[game.getPlayers().indexOf(cplayer)]+1.0)/(sum+1-continents[i].playerown[game.getPlayers().indexOf(cplayer)]);
									maxpercenttotal=(continents[i].playerown[game.getPlayers().indexOf(cplayer)]+1.0)/numberofcountries;
									minborders=numberofborders;
									mincountries=numberofcountries;
									indMax=i;
								}
								else if(abs((continents[i].playerown[game.getPlayers().indexOf(cplayer)]+1.0)/numberofcountries-maxpercenttotal)<0.0001)
								if(numberofborders<minborders)
								{   maxpercentofplayers=(continents[i].playerown[game.getPlayers().indexOf(cplayer)]+1.0)/(sum+1-continents[i].playerown[game.getPlayers().indexOf(cplayer)]);
									maxpercenttotal=(continents[i].playerown[game.getPlayers().indexOf(cplayer)]+1.0)/numberofcountries;
									minborders=numberofborders;
									mincountries=numberofcountries;
									indMax=i;
								}
								else if(numberofborders==minborders)
								if(numberofcountries<mincountries)
								{   maxpercentofplayers=(continents[i].playerown[game.getPlayers().indexOf(cplayer)]+1.0)/(sum+1-continents[i].playerown[game.getPlayers().indexOf(cplayer)]);
									maxpercenttotal=(continents[i].playerown[game.getPlayers().indexOf(cplayer)]+1.0)/numberofcountries;
									minborders=numberofborders;
									mincountries=numberofcountries;
									indMax=i;
								}
							}
						}
					}
					//We will get country on indMax continent.
					//choosing country
					int minneighbours=250;
					int maxourneighbours=0;
					int indmin=0;

					List<Country> countries=new ArrayList<>();
					countries.addAll(continents[indMax].getTerritoriesContained());
					List<Country> choosefrom=new ArrayList<>();
					for(i=0;i<countries.size();i++)
					{   int neighboursnumber=0;
						int ourneighbournumber=0;
						Country country=countries.get(i);
						List<Country> neighbours=new ArrayList<>();
						neighbours.addAll(country.getNeighbours());
						for (Country neighbour : neighbours)
						{
							if(neighbour.getOwner()!=cplayer)
								neighboursnumber++;
							else
								ourneighbournumber++;
						}
						if(neighboursnumber<minneighbours&&country.getOwner()==null)
						{   minneighbours=neighboursnumber;
							maxourneighbours=ourneighbournumber;
							indmin=i;
							if(choosefrom.size()>0)
								choosefrom.clear();
							choosefrom.add(country);
						}
						else if(neighboursnumber==minneighbours&&country.getOwner()==null)
						if(ourneighbournumber>maxourneighbours)
						{   minneighbours=neighboursnumber;
							maxourneighbours=ourneighbournumber;
							indmin=i;
							if(choosefrom.size()>0)
								choosefrom.clear();
							choosefrom.add(country);
						}
						else if(ourneighbournumber==maxourneighbours)
						{   choosefrom.add(country);
						}
					}
					Random rand = new Random();
					int rr = rand.nextInt(choosefrom.size());
					i=choosefrom.get(rr).getColor();
					return "placearmies "+i+" 1";
				}
				else
				{   //making mini-map with only continents
					int i,j,k;
					minimap=new int[l][l];
					iminimap=new int[l];
					for(i=0;i<l;i++)
					{   for(j=0;j<l;j++)
							minimap[i][j]=0;
						iminimap[i]=0;
					}
					Continent[] Minimap=game.getContinents();
					for(i=0;i<l;i++)
					{   Continent continent=Minimap[i];
						List<Country> borders=new ArrayList<>();
						borders.addAll(continent.getBorderCountries());
						for(j=0;j<borders.size();j++)
						{   List<Country> neighbours=new ArrayList<>();
							neighbours.addAll(borders.get(j).getNeighbours());
							for(k=0;k<neighbours.size();k++)
							{   Country neighbour=neighbours.get(k);
								minimap[i][iminimap[i]]=neighbour.getContinent().getColor();
								iminimap[i]++;
							}
						}
					}
					//looking for continents on which we want to take all countries with available number of territories
					int[] bestusedcontinents=new int[l];
					int minborders=260;
					for(i=0;i<l;i++)
					{   Continent continent;
						int[] usedcontinents=new int[l];
						int limit=game.getCountries().length*3/4/game.getPlayers().size()+1;
						for(j=1;j<l;j++)
							usedcontinents[j]=0;
						//backtracking
						List<Continent> list=null;
						//List<Integer> y=new ArrayList<>();
						//List<Integer> x=new ArrayList<>();
						continent=game.getContinents()[i];
						int sumofterritories=continent.getTerritoriesContained().size();
						if (sumofterritories>limit)
							continue;
						list.add(continent);
						usedcontinents[continent.getColor()]=1;
						while(list.size()>0)
						{   continent=list.get(list.size()-1);
							for(j=0;j<iminimap[continent.getColor()];j++)
							{   int id=minimap[continent.getColor()][j];
								if(sumofterritories+game.getContinents()[id].getTerritoriesContained().size()<=limit&&usedcontinents[id]==0)
								{   sumofterritories=game.getContinents()[id].getTerritoriesContained().size();
									list.add(game.getContinents()[id]);
									usedcontinents[id]=1;
									break;
								}
							}
							if(j!=iminimap[continent.getColor()])
							{   //ovde cemo sracunati broj granicnih teritorija NIJE GOTOVO!!!
								List<Country> borders=new ArrayList<>();
								List<Country> neighbours=new ArrayList<>();
								Country border;
								int sumofborders=0;
								bestusedcontinents=usedcontinents;
								usedcontinents[continent.getColor()]=0;
								list.remove(list.size()-1);
							}
						}
					}
				}
			else */
			// </editor-fold>
			if(game.Smallmap==0)
			{   game.inddefencefortification=50;
				if(cplayer.getExtraArmies()==1)
					game.indplacearmies++;
				if (game.indcontinentpriority==0)
				{   //Sastavljamo listu prioriteta kontinenata, po kojoj cemo pojacavati skoro svuda po 3.
					game.indcontinentpriority=1;
					int i,j;
					float[][] territorriespercontinentwe=new float[RiskGame.MAX_PLAYERS][l];
					float[][] territorriespercontinentenemy=new float[RiskGame.MAX_PLAYERS][l];
					for(i=0;i<l;i++)
					   for(j=0;j<p;j++)
					   {   territorriespercontinentwe[j][i]=0;
						   territorriespercontinentenemy[j][i]=0;
						   game.continentpriority[j][i]=-1;
					   }
					//Tražimo uslove pod kojima cemo odrediti prioritet kontinenata i kontinente sa jednom teritorijom.
					for(i=0;i<p;i++)
						I[i]=0;
					for(j=0;j<l;j++)
					{   Continent continent=game.getContinents()[j];
						List<Country> countries=new ArrayList<>();
						countries.addAll(continent.getTerritoriesContained());
						if(countries.size()==1)
						{   Player playeer=((Country)continent.getTerritoriesContained().get(0)).getOwner();
							i=game.getPlayers().indexOf(playeer);
							game.continentpriority[i][I[i]]=j;
							I[i]++;
						}
						else
						{   for(Country country:countries)
								territorriespercontinentenemy[game.getPlayers().indexOf(country.getOwner())][j]++;
							for(i=0;i<6;i++)
							{   territorriespercontinentenemy[i][j]/=countries.size();
								territorriespercontinentwe[i][j]=territorriespercontinentenemy[i][j]*continent.getArmyValue()/continent.getIncomingBorderCountries().size();
							}
						}
					}
					for(i=0;i<p;i++)
						K[i]=I[i];
					float max=-1;
					int indmaxi=0,indmaxj=0;
					//kontinenti koji su neprijateljima bitni
					while(5>3)
					{   for(i=0;i<p;i++)
							for(j=0;j<l;j++)
							{   if(territorriespercontinentenemy[i][j]>max)
								{   max=territorriespercontinentenemy[i][j];
									indmaxi=i;
									indmaxj=j;
								}
							}
						if((max>=(game.getContinents()[indmaxj].getTerritoriesContained().size()/2)/(float)game.getContinents()[indmaxj].getTerritoriesContained().size()&&p>3)
						||(max>=(game.getContinents()[indmaxj].getTerritoriesContained().size()*2/3)/(float)game.getContinents()[indmaxj].getTerritoriesContained().size()&&p<=3))
						{   for(i=0;i<p;i++)
								if(i!=indmaxi)
								if((territorriespercontinentenemy[i][indmaxj]>=(game.getContinents()[indmaxj].getTerritoriesContained().size()/2)/(float)game.getContinents()[indmaxj].getTerritoriesContained().size()&&p>3)
								||(territorriespercontinentenemy[i][indmaxj]>=(game.getContinents()[indmaxj].getTerritoriesContained().size()*2/3)/(float)game.getContinents()[indmaxj].getTerritoriesContained().size()&&p<=3))
								{   territorriespercontinentwe[indmaxi][indmaxj]=0;
									game.continentpriority[indmaxi][I[indmaxi]]=indmaxj;
									I[indmaxi]++;
									break;
								}
							for(i=0;i<p;i++)
								if(i!=indmaxi)
								{   territorriespercontinentwe[i][indmaxj]=0;
									game.continentpriority[i][I[i]]=indmaxj;
									I[i]++;
								}
						}
						for(i=0;i<p;i++)
							territorriespercontinentenemy[i][indmaxj]=0;
						if(max==0)
							break;
						max=0;
					}
					//kontinenti koji su nama bitni
					for(i=0;i<p;i++)
					{   for(;I[i]<l;I[i]++)
						{   max=0;
							indmaxj=0;
							for(j=1;j<l;j++)
							{   if(territorriespercontinentwe[i][j]>max)
								{   max=territorriespercontinentwe[i][j];
									indmaxj=j;
								}
							}
							game.continentpriority[i][I[i]]=indmaxj;
							territorriespercontinentwe[i][indmaxj]=0;
						}
					}
					//kontinenti sa pojacanjem 0 - oni gore nisu uracunati
					for(j=0;j<l;j++)
						if(game.getContinents()[j].getArmyValue()==0)
							I[0]--;
					for(j=0;j<l;j++)
						if(game.getContinents()[j].getArmyValue()==0)
						{   for(i=0;i<p;i++)
								game.continentpriority[i][I[0]]=j;
							I[0]++;
						}

					for(i=0;i<p;i++)
						game.countrypriority.add(new ArrayList<>());
					for(i=0;i<p;i++)
					{   List<Country> borders=new ArrayList<>();
						Player player=(Player)game.getPlayers().get(i);
						for(j=0;j<l;j++)
						{   List<Country> countries;
							int pr=game.continentpriority[i][j];
							if(j<K[i])
								borders.addAll(game.getContinents()[pr].getTerritoriesContained());
							if(pr>-1)
							{   countries=game.getContinents()[pr].getTerritoriesContained();
								for(Country country:countries)
								{   if(country.getOwner()==player)
									{   //Da li je teritorija branjena sa svih strana?
										HashSet<Country> neighbours=new HashSet<>();
										neighbours.addAll(country.getIncomingNeighbours());
										neighbours.addAll(country.getNeighbours());
										//neighbours.removeAll(player.getTerritoriesOwned());
										neighbours=removeAll(player,neighbours);
										if(neighbours.isEmpty())
											borders.add(country);
										else
											if(!game.countrypriority.get(i).contains(country.getColor()))
												game.countrypriority.get(i).add(country.getColor());
										// <editor-fold defaultstate="collapsed">
										/*int ind=0;
										for(Country neighbour:neighbours)
										{   if(neighbour.getOwner()!=player&&!countrypriority.get(i).contains(country.getColor()))
											{   countrypriority.get(i).add(country.getColor());
												ind=1;
												break;
											}
										}
										if(ind==0)
											borders.add(country);*/
										// </editor-fold>
									}
								}
							}
						}
						FindBorders(borders,player,"incoming outer");
						for(j=0;j<borders.size();j++)
						{   Country border=borders.get(j);
							game.borderids[i][j]=border.getColor();
						}
						borders.clear();
						J[i]=j;
					}
				}
			if((double)game.numberofgoodplayers/game.getPlayers().size()>0.46)
			{   int i=game.getPlayers().indexOf(cplayer);
				for(int index:game.countrypriority.get(i))
				{   Country country=game.getCountries()[index-1];
					if(country.getArmies()<3&&country.getOwner()==cplayer)
						return "placearmies "+country.getColor()+" 1";
				}
				for(int j=0;j<J[i];j++)
				{   int a=game.getCountries()[game.borderids[i][0]-1].getArmies();
					Country border=game.getCountries()[game.borderids[i][j]-1];
					if(border.getArmies()<a&&border.getOwner()==cplayer)                           
						return "placearmies "+border.getColor()+" 1";
				}        
				if(game.borderids[i][0]>0&&game.getCountries()[game.borderids[i][0]-1].getOwner()==cplayer)
					return "placearmies "+game.borderids[i][0]+" 1";                    
				else
					for(int j=0;j<game.countrypriority.get(i).size();j++)
					{   Country country=game.getCountries()[game.countrypriority.get(i).get(j)-1];
						if(country.getArmies()<game.getCountries()[game.countrypriority.get(i).get(0)-1].getArmies()&&country.getOwner()==cplayer)
							return "placearmies "+country.getColor()+" 1";
					}
				if(game.getCountries()[game.countrypriority.get(i).get(0)-1].getOwner()==cplayer)
					return "placearmies "+game.countrypriority.get(i).get(0)+" 1";  
			}}
		}
		else
		{   l=game.getCountries().length;
			p=game.getPlayers().indexOf(cplayer);
			//inddefencefortification=50;
			if(game.inddefencefortification!=p)//stvari koje se rade na pocetku poteza:
			{   game.inddefencefortification=p;
				game.indcontinentpriority=0;
				game.indfortifying=0;
				threats2=new ArrayList<>();
				fulldefended=new HashSet<>();
				betterdefence=new HashSet<>();
				worsedefence=new HashSet<>();
				extendedworsedefence=new HashSet<>();
				Borders=new HashSet<>();
				List<Player> players=game.getPlayers();
				for(int j=1;j<=l;j++)
					threats[j]=0;
				for(Player player:players)
				{   List<Country> Betterdefence1=new ArrayList<>();
					List<Country> Worsedefence1=new ArrayList<>();
					List<Country> Borders1=new ArrayList<>();
					List<Country> Borders2=new ArrayList<>();
					Borders1.addAll(FindFullDefended(player));
					Borders2.addAll(Borders1);
					FindBorders(Borders2,player,"incoming outer");
					Borders.addAll(Borders2);
					fulldefended.addAll(Borders1);
					List<Country> largestempire;
					if(game.smallmap==1||betterdefence.size()+worsedefence.size()>=game.getCountries().length/2)
					{   largestempire=getLargestEmpire(player);
						Borders1.removeAll(largestempire);
						Borders1.addAll(largestempire);
					}
					FindBorders(Borders1,player,"incoming outer");//vraca i negranicne teritorije, ako su susedne granicim, tj. produzenu granicu
					FindDefensible(Betterdefence1,Worsedefence1,player);
					betterdefence.addAll(Betterdefence1);
					/*if(smallmap==1)
						betterdefence.addAll(Worsedefence1);*/
					extendedworsedefence.addAll(Worsedefence1);
					extendedworsedefence.removeAll(Borders1);//to je produzena granica
					Borders1.removeAll(Worsedefence1);
					Borders1.addAll(Worsedefence1);
					Borders1.removeAll(betterdefence);
					worsedefence.addAll(Borders1);
				}
				worsedefence.removeAll(betterdefence);

				//Zabranjen je napad sa teritorija koje sprecavaju osvajanje kontinenta, ali je ipak dozvoljen ako drzimo ceo kontinent:
				//kontinenti koje igrac moze da osvoji:
				HashSet<Continent> continents;
				List<Integer> type=new ArrayList<>();
				//ostavljanje samo odbrane na skoro svim nasim teritorijama:
				int[] pArmies=new int[game.getCountries().length+1];//za prosledjivanje funkciji FindContinents, da ne menjamo brojeve na samoj karti
				almostconquered=new ArrayList<>();
				almostconqueredP=new ArrayList<>();
				//Pretnje se traze kasnije, medjutim, pozivaju se na skoro osvojene kontinente.
				//Kako prvo njih trazimo, potrebno je ocistiti pretnje od toga.
				threats=FindThreats(cplayer);
				for(Country country:game.getCountries())
				{   double threat=threats[country.getColor()];
					if(country.getOwner()==cplayer)
					{   if(betterdefence.contains(country))
						{   threat=Math.min(threat,country.getArmies());
							threat=Math.max(threat,3);
							pArmies[country.getColor()]=(int)threat;
						}
						else if(worsedefence.contains(country))
						{   threat=threat*2/3;
							threat=Math.min(threat,country.getArmies());
							threat=Math.max(threat,3);
							pArmies[country.getColor()]=(int)threat;
						}
						else
						{   if((int)3>=country.getArmies())
								continue;
							pArmies[country.getColor()]=3;
						}
					}
					else
						pArmies[country.getColor()]=country.getArmies();
				}
				for(Player player:players)
				{   if(player==cplayer)
						continue;
					continents=new HashSet<>();
					continents.addAll(FindContinents2(getReinforcements(player),player,type,pArmies));
					if(type.get(0)==1)
						for(Continent continent:continents)
							if(!almostconquered.contains(continent))
							{   almostconquered.add(continent);
								almostconqueredP.add(player);
							}
				}
				for(Player player:players)
				{   //kontinenti kojih igrac drzi bar 2/3:
					for(Continent continent:game.getContinents())
					{   HashSet<Country> Countries=new HashSet<>();
					//	HashSet<Country> ourcountries;
						Countries.addAll(continent.getTerritoriesContained());
						//Countries.retainAll(player.getTerritoriesOwned());
						Countries=retainAll(player,Countries);
						if(Countries.size()*3>=(continent.getTerritoriesContained().size()-1)*2&&Countries.size()<continent.getTerritoriesContained().size())
							if(!almostconquered.contains(continent))
							{   almostconquered.add(continent);
								almostconqueredP.add(player);
							}
					}
				}
				threats=new double[256];
				for(Player player:players)
				{   //trazimo pretnje:
					//HashSet<Country> Betterdefence=new HashSet<>();
					//HashSet<Country> Worsedefence=new HashSet<>();
					//Betterdefence.addAll(betterdefence);
					//Worsedefence.addAll(worsedefence);
					//HashSet<Country> Betterdefence=retainAll(player,betterdefence);
					//HashSet<Country> Worsedefence=retainAll(player,worsedefence);
					double[] Threats=new double[255];
					for(int j=1;j<=l;j++)
						Threats[j]=0;
					Threats=FindThreats(player);
					for(int j=1;j<=l;j++)
					threats[j]+=Math.max(Threats[j],threats[j]);
					for(int j=1;j<=l;j++)
					{   Country country=game.getCountries()[j-1];
						if(worsedefence.contains(country))
						{   
							Threats[j]=Math.max(6,Threats[j]+2.25);
							threats1[j]=Threats[j]*2/3-country.getArmies();
						}
						else if(betterdefence.contains(country))
						{   /*if(fulldefended.contains(country))
								threats1[j]=Math.max(6,Threats[j]*1.6+2);
							else*/
								threats1[j]=Math.max(6,Threats[j]+2);
							threats1[j]-=country.getArmies();
							threats1[j]=Math.max(0,threats1[j]);
						}
						else
							threats1[j]=0;
					}
					for(int j=1;j<=l;j++)
						threats[j]+=Math.max(threats[j],0);
				}
				//ODBRAMBENO POJACANJE
				//List<Country> Betterdefence=new ArrayList<>();
				//Betterdefence.addAll(retainAll(cplayer,betterdefence));
				//FindDefensible(Betterdefence,Worsedefence,cplayer);
				//if(smallmap==1)
				//    Betterdefence.addAll(Worsedefence);
				//sortiranje
				for(int j=1;j<=l;j++)
					indthreats[j]=j;
				for(int i=1;i<=l-1;i++)
				{   int ind=0,P;
					double max=0;
					for(int j=i+1;j<=l;j++)
						if(threats1[j]>max)
						{   max=threats1[j];
							ind=j;
						}
					if(max==0)
						break;
					if(max>threats1[i])
					{   threats1[ind]=threats1[i];
						threats1[i]=max;
						P=indthreats[i];
						indthreats[i]=indthreats[ind];
						indthreats[ind]=P;
					}
				}
			}
			//pojacavanje teritorija sa prioritetom:
			l=game.getCountries().length;
			for(int i=1;i<l;i++)
				if(threats1[1]/threats1[i]>=10&&threats1[i]>4&&game.getCountries()[indthreats[i]-1].getOwner()==cplayer)
				if(betterdefence.contains(game.getCountries()[indthreats[i]-1]))
				{   threats1[i]--;
					return "placearmies "+indthreats[i]+" "+1;
				}
			for(int i=1;i<l;i++)
				if(threats1[i]>=1&&threats1[i]>=threats1[i+1]&&game.getCountries()[indthreats[i]-1].getOwner()==cplayer)
				if(betterdefence.contains(game.getCountries()[indthreats[i]-1]))
				{   threats1[i]--;
					return "placearmies "+indthreats[i]+" "+1;
				}
			if(threats1[1]>=1&&game.getCountries()[indthreats[1]-1].getOwner()==cplayer)
			if(betterdefence.contains(game.getCountries()[indthreats[1]-1]))
			{   threats1[1]--;
				return "placearmies "+indthreats[1]+" "+1;
			}
			//nastavak:
			Country country;
			int armies;
			while(!tofortify1.isEmpty()&&!tofortify2.isEmpty())
			{   country=tofortify1.get(0);
				tofortify1.remove(0);
				armies=tofortify2.get(0);
				tofortify2.remove(0);
				if(armies>cplayer.getExtraArmies())
					armies=cplayer.getExtraArmies();
				if((country.getOwner()==cplayer)&&(armies>0)&&(armies<=cplayer.getExtraArmies()))
					return "placearmies "+country.getColor()+" "+armies;
			}
			if(tofortify1.isEmpty()/*&&toattack.isEmpty()*/)
			{   game.indfortifying++;
				if(game.indfortifying==1)
				{   plan1();
					if(tofortify1.isEmpty())
						game.indfortifying++;
				}
				if(game.indfortifying==2)
				{   plan2();
					if(tofortify1.isEmpty())
						game.indfortifying++;
				}
				if(game.indfortifying>2)
				{   game.indfortifying=0;
					plan();
				}
			}
			while(!tofortify1.isEmpty()&&!tofortify2.isEmpty())
			{   country=tofortify1.get(0);
				tofortify1.remove(0);
				armies=tofortify2.get(0);
				tofortify2.remove(0);
				if(armies>cplayer.getExtraArmies())
					armies=cplayer.getExtraArmies();
				if((country.getOwner()==cplayer)&&(armies>0)&&(armies<=cplayer.getExtraArmies()))
					return "placearmies "+country.getColor()+" "+armies;
			}
			//armies=0;
		}

		if (((this.type == AIDomination.PLAYER_AI_EASY && game.NoEmptyCountries() && r.nextInt(6) != 0) //mostly random placement
		/*|| (game.getSetupDone() && this.type == AIDomination.PLAYER_AI_AVERAGE && r.nextBoolean())*/)) { //use a random placement half of the time to make the player less aggressive
			return simplePlacement();
		}
		if ( game.NoEmptyCountries() )
		{   if(this.type==AIDomination.PLAYER_AI_AVERAGE)
				try
				{   tofortify1.add(toattack.get(0));
					tofortify2.add(cplayer.getExtraArmies());
				}
				catch(Exception e)
				{
					return plan(false);
				}
			else
				return plan(false);
		}
		return findEmptyCountry();
    }   

@Override
	public String getAttack() {
		game.inddefencefortification=50;
		eliminating = false;
		breaking = null;
		String result="",Result="";
		tofortify1.clear();
		tofortify2.clear();
		int count=0;
		if(cplayer.getType()==AIDomination.PLAYER_AI_AVERAGE&&game.getCardMode()==RiskGame.CARD_ITALIANLIKE_SET/*&&smallmap==0*/)
		{   if(indroll==1)
			{   indroll=0;
				if(!threats2.isEmpty())
				{   try{
						int attackcolor=toattack.get(0).getColor();
						int defendcolor=todefend.get(0).getColor();
						threats2.set(attackcolor,new ArrayList<>());
						threats2.get(attackcolor).add(0.0);
						threats2.get(attackcolor).addAll(FindThreats(cplayer,toattack.get(0)));
						threats2.set(defendcolor,new ArrayList<>());
						threats2.get(defendcolor).add(0.0);
						threats2.get(defendcolor).addAll(FindThreats(cplayer,todefend.get(0)));
					}catch(Exception e){
						indroll=0;
					}
				}
				else
				{   Country[] countries=game.getCountries();
					HashSet<Country> neighbours=new HashSet<>();
					List<Country> ourcountries=cplayer.getTerritoriesOwned();
					for(Country country:ourcountries)
						neighbours.addAll(country.getNeighbours());
					neighbours=removeAll(cplayer,neighbours);
					threats2.add(new ArrayList<>());
					for(int i=0;i<countries.length;i++)
					{   threats2.add(new ArrayList<>());
						if(neighbours.contains(countries[i]))
							threats2.get(i+1).add(FindThreats(cplayer,countries[i],countries[i]));
						else
							threats2.get(i+1).add(0.0);
						if(countries[i].getOwner()==cplayer)
							threats2.get(i+1).addAll(FindThreats(cplayer,countries[i]));
					}
				}
				toattack.remove(0);
				todefend.remove(0);
				attacktype.remove(0);
				towinmove.remove(0);
				towinstay.remove(0);
			}
			while(true)
			{   if(toattack.isEmpty())
				{   plan2();
					plan();
					count=0;
				}
				if(toattack.isEmpty())
					return "endattack";
				Country attacker,defender,toattack0=null,todefend0=null;
				if(!toattack.isEmpty())
				{   toattack0=toattack.get(0);
					todefend0=todefend.get(0);
				}
				//prvi u listi napada moze biti uslovljen nekim iza, ali ima nizi parametar, pa se odlaze i stavlja na kraj liste.
				attacker=toattack.get(0);
				defender=todefend.get(0);
				if(attacker.getOwner()!=cplayer||defender.getOwner()==cplayer||!attacker.isNeighbours(defender)||attacker.getArmies()<=1)
				{   toattack.remove(0);
					todefend.remove(0);
					attacktype.remove(0);
					towinmove.remove(0);
					towinstay.remove(0);
					continue;
				}
				int Defend=defender.getArmies();
				int move=towinmove.get(0);
				int stay=towinstay.get(0);
				int type=attacktype.get(0);
				if(stay==0)
					stay=1;
				if(stay==2)
					stay=3;
				if(move==2)
					move=3;
				if(stay<=1&&type>=0)
				{   HashSet<Country> neighbours=new HashSet<>();
					neighbours.addAll(attacker.getNeighbours());
					//neighbours.removeAll(cplayer.getTerritoriesOwned());
					neighbours=removeAll(cplayer,neighbours);
					Country conditionneighbour=null;
					for(Country neighbour:neighbours)
						if(neighbour!=defender&&todefend.contains(neighbour))
						{   conditionneighbour=neighbour;
							break;
						}
					if(conditionneighbour!=null)
					{   if(neighbours.size()>1)
						{   toattack.add(toattack.get(0));
							todefend.add(todefend.get(0));
							towinstay.add(towinstay.get(0));
							towinmove.add(towinmove.get(0));
							attacktype.add(attacktype.get(0));
							toattack.remove(0);
							todefend.remove(0);
							attacktype.remove(0);
							towinmove.remove(0);
							towinstay.remove(0);
							if((toattack0==attacker)&&(todefend0==defender))
							{   count++;
								if(count<=toattack.size())
									continue;
							}
						}
					}
					//da li je prekinut deo plana koji utice na ovaj napad, u slucaju pomeranja jedne granice:
					else if(neighbours.size()>1)
					{   double threat2=FindThreats(cplayer,attacker,defender);
						double threat3=FindThreats(cplayer,defender,defender);
						if(towinmove.get(0)<0||towinstay.get(0)<0)
						{   threat2=threat2*2/3;
							threat3=threat3*2/3;
						}
						if(Math.round(threat2)>towinstay.get(0))
							towinstay.set(0,(int)Math.round(threat2));
						else
							if(towinmove.get(0)<0||towinstay.get(0)<0)
								towinstay.set(0,3);
							else
								towinstay.set(0,6);
						if(Math.round(threat3)>towinmove.get(0))
							towinmove.set(0,(int)Math.round(threat3));
						// <editor-fold defaultstate="collapsed">
						/*List<Country> fulldefended1=new ArrayList<>();
						fulldefended1.addAll(fulldefended);
						fulldefended1.retainAll(cplayer.getTerritoriesOwned());
						List<Country> borders=new ArrayList<>();
						borders.addAll(fulldefended1);
						FindBorders(borders,cplayer,"outer");
						if(borders.contains(attacker))
						{   neighbours=new HashSet<>();
							neighbours.addAll(attacker.getIncomingNeighbours());
							neighbours.removeAll(fulldefended1);
							neighbours.retainAll(cplayer.getTerritoriesOwned());
							for(Country neighbour:neighbours)
								//ako posle pomeranja granice na jednoj od novih granica nece biti dovoljno tenkova, ne premesta se sve:
								if(!fulldefended1.contains(neighbour)&&(towinstay.get(0)<=1))
								{   double threat2=FindThreats(cplayer,neighbour,neighbour);
									double threat3=FindThreats(cplayer,attacker,neighbour);
									if(towinmove.get(0)<0||towinstay.get(0)<0)
									{   threat2=threat2*2/3;
										threat3=threat3*2/3;
									}
									if(neighbour.getArmies()<threat2&&neighbour.getArmies()<threat3)
										towinstay.set(0,(int)Math.round(threat3));
								}
						}
						else
							towinstay.set(0,3);*/
						// </editor-fold>
					}
				}
				if(towinmove.get(0)<0||towinstay.get(0)<0)
				{   towinstay.set(0,-towinstay.get(0));
					towinmove.set(0,-towinmove.get(0));
				}
				int attack=attacker.getArmies();
				//da li je u pitanju napad vise na jedan:
				int attack1=attack;
				if(attack>3&&toattack.size()>1)
				{   for(int i=1;i<toattack.size();i++)
						{   if(todefend.get(i)==defender)
							{   attack+=toattack.get(i).getArmies()-towinmove.get(i)-towinstay.get(i)-attacktype.get(i);
								move-=toattack.get(i).getArmies()-towinmove.get(i)-towinstay.get(i)-attacktype.get(i);
							}
						}
					if(move<3)
						move=3;
				}
				//ako je napad jedinstven od napadaca ili je branilac opkoljen (ovo drugo vise ne):
				HashSet<Country> neighbours;
				//ako je napad jedinstven od napadaca:
				if(attack<=7&&attack-defender.getArmies()>=3&&attacktype.get(0)<=0)
				{   if(attack==4)
						attack=5;
					neighbours=new HashSet<>();
					//neighbours.addAll(attacker.getNeighbours());
					neighbours.addAll(attacker.getIncomingNeighbours());
					neighbours.remove(defender);
					//neighbours.removeAll(attacker.getOwner().getTerritoriesOwned());
					neighbours=removeAll(attacker.getOwner(),neighbours);
					if(attack!=6||defender.getArmies()!=3)
					if(neighbours.isEmpty())
						attack=8;
				}
				double Threat=0;
				if(type>=0)
				{   Threat=FindThreats(cplayer,defender,attacker);
					if(betterdefence.contains(attacker));
					else if(worsedefence.contains(attacker))
						Threat*=2.0/3;
					else
						Threat=Defend+move;
					Threat+=2;
				}
				if(type<0)
					type=0;
				if((Defend>type&&((attack>=3+Defend&&attack>Math.min(stay,3)+Math.min(move,3)+1-Math.max(3-Defend,0))||(type>0&&attack>=Defend)))
				&&(((Defend<3&&attack+1>=Defend+stay+move)||(Defend>=3&&attack+1>=stay+Threat)||(type>0&&attack>=Math.max(Defend,stay)))&&(attack>=6||(Defend<3&&attack>=stay+3)))
				&&(attack1>=move+stay&&((attack1>=6&&/**/attack1>=Defend)||(/**/attack1<6&&attack1-Defend>=3))&&defender.isNeighbours(attacker)))
				{   result="attack "+attacker.getColor()+" "+defender.getColor();
					if(!CheckRepeatedAttack1(result))
					{   indroll=0;
						return result;
					}
					else
					{   Result=result;
						break;
					}
				}
				else
				{   result="attack "+attacker.getColor()+" "+defender.getColor();
					if(CheckRepeatedAttack1(result))
						return "endattack";
				}
				toattack.remove(0);
				todefend.remove(0);
				attacktype.remove(0);
				towinmove.remove(0);
				towinstay.remove(0);
			}
		}

		if(!result.equals("")&&!result.equals(Result))
			if(CheckRepeatedAttack(result))
				return "endattack";
			else
			{   indroll=0;
				return result;
			}

		result=plan(true);
		if(result.equals(Result))
			if(CheckRepeatedAttack(result))
				return "endattack";
		if(cplayer.getType()!=AIDomination.PLAYER_AI_AVERAGE)
			return result;
		else
			return "endattack";
	}

	/**
	 * Will roll the maximum, but checks to see if the attack is still the
	 * best plan every 3rd roll
         * @return 
	 */
        @Override
            public String getRoll() {
                Defender=game.getDefender().getOwner();
                if(Defence==0)
                    Defence=game.getDefender().getArmies();
				int n=game.getAttacker().getArmies() - 1;
				int m=game.getDefender().getArmies();
                if(!toattack.isEmpty())
                {   int stay=towinstay.get(0);//koliko mora da ostane
                    int stay1;
                    int move=towinmove.get(0);//koliko mora da se premesti
                    int type=attacktype.get(0);//koliko odbrani mora da ostane
                    int attack=game.getAttacker().getArmies();
                    int attack1=game.getAttacker().getArmies();
                    int Defend=game.getDefender().getArmies();
                    if(stay==2)
                        stay=3;
                    if(stay==0)
                    {   stay=1;
                        stay1=0;
                    }
                    if(move<3)
                        move=3;
                    //da li je u pitanju napad vise na jedan:
                    Country attacker=game.getAttacker();
                    Country defender=game.getDefender();
                    if(attack>3&&toattack.size()>1)
                    {   for(int i=1;i<toattack.size();i++)
                            {   if(todefend.get(i)==defender)
                                {   attack+=toattack.get(i).getArmies()-towinmove.get(i)-towinstay.get(i)-attacktype.get(i);
                                    move-=toattack.get(i).getArmies()-towinmove.get(i)-towinstay.get(i)-attacktype.get(i);
                                }
                            }
                        if(move<3)
                            move=3;
                    }
                    //ako je napad jedinstven od napadaca ili je branilac opkoljen (ovo drugo vise ne):
                    HashSet<Country> neighbours;
                    if(attack<=7&&attack-Defend>=3&&type<=0)
                    {   if(attack==4)
                            attack=5;
                        neighbours=new HashSet<>();
                        //neighbours.addAll(attacker.getNeighbours());
                        neighbours.addAll(attacker.getIncomingNeighbours());
                        neighbours.remove(defender);
                        //neighbours.removeAll(attacker.getOwner().getTerritoriesOwned());
                        neighbours=removeAll(attacker.getOwner(),neighbours);
                        if(attack!=6||Defend!=3)
                        if(neighbours.isEmpty())
                            attack=8;
                    }
                    double Threat=0;
                    if(type>=0)
                    {   Threat=FindThreats(cplayer,defender,attacker);
                        if(betterdefence.contains(attacker));
                        else if(worsedefence.contains(attacker))
                            Threat*=2.0/3;
                        else
                            Threat=Defend+move;
                        Threat+=2;
                    }
                    if(type<0)
                        type=0;
                    if(Defend>type&&((attack>=3+Defend&&attack>Math.min(stay,3)+Math.min(move,3)+1-Math.max(3-Defend,0))||(type>0&&attack>=Defend)))
                    //Prvi uslov (tj. prva 2) je komplikovan. Treba ga svesti na attack+1>=stay+x. Medjutim, x nije jedinstveno odredjeno.
                    //Ako zelimo da samo mi osvojimo, ne treba skidati vise od pretnje. To cemo trenutno staviti.
                    //Ako zelimo da bilo ko osvoji (npr. borba protiv najjaceg igraca ili skidanje kontinenta, skidamo kol'ko mozemo, cuvajuci napadaca od pretnje.
                    if(((Defend<3&&attack+1>=Defend+stay+move)||(Defend>=3&&attack+1>=stay+Threat)||(type>0&&attack>=Math.max(Defend,stay)))&&(attack>=6||(Defend<3&&attack>=stay+3)))
                    if(attack1>=move+stay&&((attack1>=6&&/**/attack1>=Defend)||(/**/attack1<6&&attack1-Defend>=3))&&defender.isNeighbours(attacker))
                    {   indroll=1;
                        return "roll " + Math.min(3, n);
                    }
                    if(indroll==1)
                    {   //threats2[todefend.get(0).getColor()]=FindThreats(cplayer,todefend.get(0),todefend.get(0));
                        indroll=0;
                        if(!threats2.isEmpty())
                            try{
                                int attackcolor=game.getAttacker().getColor();
                                int defendcolor=game.getDefender().getColor();
                                threats2.set(attackcolor,new ArrayList<>());
                                threats2.get(attackcolor).add(0.0);
                                threats2.get(attackcolor).addAll(FindThreats(cplayer,toattack.get(0)));
                                threats2.set(defendcolor,new ArrayList<>());
                                threats2.get(defendcolor).add(FindThreats(cplayer,todefend.get(0),todefend.get(0)));
                            }
                            catch(Exception e){
                                indroll=1;
                            }
                        else
                        {   Country[] countries=game.getCountries();
                            neighbours=new HashSet<>();
                            List<Country> ourcountries=cplayer.getTerritoriesOwned();
                            for(Country country:ourcountries)
                                neighbours.addAll(country.getNeighbours());
                            neighbours=removeAll(cplayer,neighbours);
                            threats2.add(new ArrayList<>());
                            for(int i=0;i<countries.length;i++)
                            {   threats2.add(new ArrayList<>());
                                if(neighbours.contains(countries[i]))
                                    threats2.get(i+1).add(FindThreats(cplayer,countries[i],countries[i]));
                                else
                                    threats2.get(i+1).add(0.0);
                                if(countries[i].getOwner()==cplayer)
                                    threats2.get(i+1).addAll(FindThreats(cplayer,countries[i]));
                            }
                        }
                    }
                    toattack.remove(0);
                    todefend.remove(0);
                    attacktype.remove(0);
                    towinmove.remove(0);
                    towinstay.remove(0);
                    return "retreat";
                }

		if (n < 3 && game.getBattleRounds() > 0 && (n < m || (n == m && game.getDefender().getOwner().getTerritoriesOwned().size() != 1))) {
			if(!toattack.isEmpty())
			if(toattack.get(0)==game.getAttacker()&&todefend.get(0)==game.getDefender())
			{   toattack.remove(0);
				todefend.remove(0);
				attacktype.remove(0);
				towinmove.remove(0);
				towinstay.remove(0);
			}
			return "retreat";
		}

		//spot check the plan
		if (type != AIDomination.PLAYER_AI_EASY && (game.getBattleRounds()%3 == 2 || (game.getBattleRounds() > 0 && (n - Math.min(m, game.getMaxDefendDice()) <= 0)))) {
			String result = plan(true);
			//TODO: rewrite to not use string parsing
			if (result.equals("endattack")) {
					if(!toattack.isEmpty())
					if(toattack.get(0)==game.getAttacker()&&todefend.get(0)==game.getDefender())
					{   toattack.remove(0);
						todefend.remove(0);
						attacktype.remove(0);
						towinmove.remove(0);
						towinstay.remove(0);
					}
					return "retreat";
			}
			StringTokenizer st = new StringTokenizer(result);
			st.nextToken();
			if (game.getAttacker().getColor() != Integer.parseInt(st.nextToken())
							|| game.getDefender().getColor() != Integer.parseInt(st.nextToken())) {
					if(!toattack.isEmpty())
					if(toattack.get(0)==game.getAttacker()&&todefend.get(0)==game.getDefender())
					{   toattack.remove(0);
						todefend.remove(0);
						attacktype.remove(0);
						towinmove.remove(0);
						towinstay.remove(0);
					}
					return "retreat";
			}
		}
		return "roll " + Math.min(3, n);

	}

	/**
	 * Takes several passes over applicable territories to determine the tactical move.
	 * 1. Find all countries with more than the min placement and do the best border fortification possible.
	 *  1.a. If there is a common threat see if we can move off of a continent we don't want
	 * 2. Move the most troops to the battle from a non-front country.
	 * 3. just move from the interior - however this doesn't yet make a smart choice.
     * @return 
	 */
        @Override
 	public String getTacMove() {
		List<Country> t = cplayer.getTerritoriesOwned();
		Country sender = null;
		Country receiver = null;
		int lowestScore = Integer.MAX_VALUE;
		GameState gs = getGameState(cplayer, false);
		//fortify the border
		List<Country> v = getBorder(gs);
		List<Country> filtered = new ArrayList<>();
		
		CreateAlliance();

		List<Continent> targetContinents = null;

		toattack.clear();
		todefend.clear();
		attacktype.clear();
		towinmove.clear();
		towinstay.clear();
		
		//racunamo prosek tenkova na granicama da bi se nagomilani tenkovi (autlajeri) premestili negde drugde:
		double sum=0;
		int count=0;
		for(Player player:(List<Player>)game.getPlayers())
		{	List<Country> borders = FindFullDefended(player);
			FindBorders(borders,player,"outer");
			for(Country border:borders)
			{	sum+=border.getArmies();
				count++;
			}
		}
		sum/=count;
		List<Country> borders = new ArrayList<>();
		borders.addAll(cplayer.getTerritoriesOwned());
		FindBorders(borders,cplayer,"outer");
		for(Country attacker:borders)
			if(attacker.getArmies()>sum*4 && attacker.getArmies()-(int)threats[attacker.getColor()]-1>0)
			{   List<Country> empire=getConnectedEmpire(attacker);
				empire.removeAll(fulldefended);
				empire.remove(attacker);
				if(!empire.isEmpty())
				{	double min=Double.POSITIVE_INFINITY;
					Country indmin=empire.get(0);
					for(int i=0;i<empire.size();i++)
					{	Country destination = empire.get(i);
						double threat = FindThreats(cplayer, destination, destination);
						if(destination.getArmies()-threat < min)
						{   min=destination.getArmies()-threat;
							indmin=destination;
						}
					}
					game.tomoveFrom.add(attacker);
					game.tomoveTo.add(indmin);
				}
			}
			
		if(cplayer.getType()==AIDomination.PLAYER_AI_AVERAGE&&game.getCardMode()==RiskGame.CARD_ITALIANLIKE_SET/*&&smallmap==0*/)
		{   //deblokiranje karata:
			List<Country> countries;
			for(int i=0;i<game.tomoveFrom.size();i++)
			{   Country From=game.tomoveFrom.get(i);
				if(From.getOwner()!=cplayer)
					continue;
				double threat=threats[game.tomoveTo.get(i).getColor()];
				if(betterdefence.contains(From))
					threat=threat*5/4;
				if(From.getArmies()<=threat)
				{   game.tomoveFrom.remove(i);
					game.tomoveTo.remove(i);
					continue;
				}
				if(Risk.inout[From.getColor()]<=0&&!game.tomoveTo.isEmpty())
				{   //trazimo put:
					Country[] from=new Country[game.getCountries().length+1];
					countries=new ArrayList<>();
					countries.add(From);
					Country country;
					if(!countries.isEmpty())
					{   prvapetlja:
						while(true)
						{   country=countries.get(0);
							HashSet<Country> neighbours=new HashSet<>();
							neighbours.addAll(country.getNeighbours());
							//neighbours.retainAll(fulldefended);
							neighbours=retainAll(cplayer,neighbours);
							for(Country neighbour:neighbours)
								if(from[neighbour.getColor()]==null)
								{   from[neighbour.getColor()]=country;
									countries.add(neighbour);
									if(game.tomoveTo.size()>i)
									if(neighbour==game.tomoveTo.get(i))
										break prvapetlja;
								}
							countries.remove(0);
							if(countries.isEmpty())
								break;
						}
						if(country.isNeighbours(game.tomoveTo.get(i)))
						{   country=game.tomoveTo.get(i);
							if(from[country.getColor()]!=null&&from!=null)
							while(From!=from[country.getColor()])
								country=from[country.getColor()];
							if(Risk.inout[From.getColor()]>0||Risk.inout[country.getColor()]<0)
								break;
							if(country==game.tomoveTo.get(i))
							{   game.tomoveFrom.remove(i);
								game.tomoveTo.remove(i);
								i--;
							}
							else
								game.tomoveFrom.set(i,country);
							return "movearmies " + From.getColor() + " " + country.getColor() + " " + (From.getArmies()-Math.max((int)threat,3));
						}
						else
						{   game.tomoveFrom.remove(i);
							game.tomoveTo.remove(i);
							i--;
						}
					}
				}
			}
				

			//optimizacija na granici:
			countries=new ArrayList<>();//to
			List<Country> countries1=new ArrayList<>();//from
			countries.addAll(worsedefence);
			countries.addAll(betterdefence);
			countries=retainAll(cplayer,countries);
			countries.removeAll(extendedworsedefence);
			countries1.addAll(countries);
			countries.removeAll(fulldefended);
			countries1.addAll(fulldefended);
			countries1=retainAll(cplayer,countries1);
			for(int i=0;i<countries.size();i++)
			{   Country country=countries.get(i);
				if(Risk.inout[country.getColor()]<0)
				{   countries.remove(i);
					i--;
				}
			}
			for(int i=0;i<countries1.size();i++)
			{   Country country=countries1.get(i);
				if(Risk.inout[country.getColor()]>0)
				{   countries1.remove(i);
					i--;
				}
			}
			for(int i=0;i<countries.size()-1;i++)
			{   Country country=countries.get(i);
				double threat=threats[country.getColor()]+2.25;
				if(betterdefence.contains(country))
				{   threat=Math.max(threat,6);
					threat=threat-country.getArmies();
				}
				else
					threat=threat*2/3-country.getArmies();
				double max=threat;
				int ind=country.getColor();
				for(int j=i+1;j<countries.size();j++)
				{   Country country1=countries.get(j);
					double threat1=threats[country1.getColor()]+2.25;
					if(betterdefence.contains(country1))
					{   threat1=Math.max(threat1,6);
						threat1=threat1-country1.getArmies();
					}
					else
						threat1=threat1*2/3-country1.getArmies();
					if(threat1>max)
					{   max=threat1;
						ind=j;
					}
				}
				if(max>threat)
				{   //country=countries.get(i);
					countries.set(i,countries.get(ind));
					countries.set(ind,country);
				}
			}
			for(Country country:countries)
			{   double threatc=threats[country.getColor()]+2.25;
				if(betterdefence.contains(country))
				{   threatc=Math.max(threatc,6);
					threatc=threatc-country.getArmies();
				}
				else
					threatc=threatc*2/3-country.getArmies();
				if(threatc<1)
					break;
				HashSet<Country> neighbours=new HashSet<>();
				neighbours.addAll(country.getIncomingNeighbours());
				neighbours=retainAll(cplayer,neighbours);
				neighbours.retainAll(countries1);
				double min=Double.POSITIVE_INFINITY;
				int move;
				Country indmin=null;
				for(Country neighbour:neighbours)
				{   double threatn=threats[neighbour.getColor()]+2.25;
					if(betterdefence.contains(neighbour))
					{   threatn=Math.max(threatn,6);
						threatn=threatn-neighbour.getArmies();
					}
					else
						threatn=threatn*2/3-neighbour.getArmies();
					if(threatn<min)
					{   min=threatn;
						indmin=neighbour;
					}
				}
				if(indmin==null)
					break;
				move=(int)(Math.round(threatc-min)/2);
				threatc=(int)(threatc)+1;
				if(move>(int)threatc)
					move=(int)threatc;
				if(indmin.getArmies()-move<3&&!fulldefended.contains(indmin))
					move=indmin.getArmies()-3;
				if(move>=indmin.getArmies())
					move=indmin.getArmies()-1;
				if(move>0&&Risk.inout[indmin.getColor()]<=0&&Risk.inout[country.getColor()]>=0)
					return "movearmies " + indmin.getColor() + " " + country.getColor() + " " + move;
			}

			//premestanje izmedju unutrasnjih teritorija u one sto imaju manje od 3 tenka:
			countries=new ArrayList<>();
			countries.addAll(cplayer.getTerritoriesOwned());
			Country indmax=null;
			for(int i=0;i<countries.size();i++)
			{   Country country=countries.get(i);
				if(Risk.inout[country.getColor()]<0)
				{   countries.remove(i);
					i--;
				}
			}
			for(Country country:countries)
				if(country.getArmies()==1)
				{   HashSet<Country> neighbours=new HashSet<>();
					neighbours.addAll(country.getIncomingNeighbours());
					neighbours=retainAll(cplayer,neighbours);
					if(fulldefended.contains(country))
						neighbours.retainAll(fulldefended);
					int max=0;
					indmax=null;
					double threat=0;
					for(Country neighbour:neighbours)
					{   if(betterdefence.contains(neighbour))
						{   threat=threats[neighbour.getColor()];
							threat=Math.max(threat,6);
						}
						if(neighbour.getArmies()-threat>max&&neighbour.getArmies()>3&&Risk.inout[neighbour.getColor()]<=0)
						{   max=neighbour.getArmies()-(int)threat;
							indmax=neighbour;
						}
					}
					if(indmax!=null&&Risk.inout[indmax.getColor()]<=0&&Risk.inout[country.getColor()]>=0)
						return "movearmies " + indmax.getColor() + " " + country.getColor() + " " + (int)Math.min(3-country.getArmies(),indmax.getArmies()-3);
				}
			for(Country country:countries)
				if(country.getArmies()==2)
				{   HashSet<Country> neighbours=new HashSet<>();
					neighbours.addAll(country.getIncomingNeighbours());
					neighbours=retainAll(cplayer,neighbours);
					if(fulldefended.contains(country))
						neighbours.retainAll(fulldefended);
					int max=0;
					indmax=null;
					for(Country neighbour:neighbours)
						if(neighbour.getArmies()>max&&neighbour.getArmies()>4&&Risk.inout[neighbour.getColor()]<=0)
						{   max=neighbour.getArmies();
							indmax=neighbour;
						}
					if(indmax!=null&&Risk.inout[indmax.getColor()]<=0&&Risk.inout[country.getColor()]>=0)
						return "movearmies " + indmax.getColor() + " " + country.getColor() + " " + 1;
				}

			//move from the interior (very very very very smart)
			HashSet<Country> fulldefended=new HashSet<>();
			int maxfulldefended=(int)Double.NEGATIVE_INFINITY;
			double indthreat=0;
			countries=new ArrayList<>();
			countries.addAll(cplayer.getTerritoriesOwned());
			for(int i=0;i<countries.size();i++)
			{   Country country=countries.get(i);
				if(Risk.inout[country.getColor()]>0)
				{	countries.remove(i);
					i--;
				}
			}
			boolean svinajednog=game.alliance.size()+1==game.getPlayers().size() && game.alliance.contains(cplayer);
			for(Country country:countries)
			{   HashSet<Country> neighbours=new HashSet<>();
				neighbours.addAll(country.getIncomingNeighbours());
				neighbours.addAll(country.getNeighbours());
				int ind=0;
				for(Country neighbour:neighbours)
				{   if((neighbour.getOwner()!=cplayer && !svinajednog) ||
					(!game.alliance.contains(neighbour.getOwner()) && svinajednog))
					{   ind=1;
						break;
					}
				}
				if(ind==0)
					fulldefended.add(country);
			}
			
			//Ako postoji ubedljivo najjaci igrac, sve snage se usmeravaju ka najblizoj granici sa njim:
			if(svinajednog)
			{	for(Country country:fulldefended)
				    if(country.getArmies()>maxfulldefended)
					{   maxfulldefended=country.getArmies();
						indmax=country;
					}
				if(indmax!=null&&Risk.inout[indmax.getColor()]>0)
				{	sender=indmax;
					HashSet<Country> neighbours=new HashSet<>();
					neighbours.add(indmax);
					HashSet<Country> notfulldefended=new HashSet<>();
					double min = Double.POSITIVE_INFINITY;
					int paths[]=new int[game.getCountries().length+1];
					try{
						paths[indmax.getColor()]=-1;
					}catch(Exception e){
						int a=0;
					}
					while(true)
					{	int ind=0;
						HashSet<Country> neighbours1=new HashSet<>();
						for(Country country:neighbours)
						{	if(game.alliance.contains(country.getOwner()) && country.getOwner()!=cplayer)
								continue;
							if(!fulldefended.contains(country))
							{	notfulldefended.add(country);
								ind=1;
							}
							else
								for(Country neighbour:(List<Country>)country.getNeighbours())
									if(paths[neighbour.getColor()]==0)
									{	paths[neighbour.getColor()]=country.getColor();
										neighbours1.add(neighbour);
									}
						}
						if(ind==1 || neighbours1.isEmpty())
							break;
						neighbours=neighbours1;
					}
					for(Country country:notfulldefended)
					{	neighbours=new HashSet<>();
						neighbours.addAll(country.getNeighbours());
						for(Country neighbour:neighbours)
							if(neighbour.getArmies()<min && !game.alliance.contains(neighbour.getOwner()))
							{	min=neighbour.getArmies();
								indmax=country;
							}
					}
					while(sender!=indmax)
					{	
						Country country = (Country)game.getCountries()[paths[indmax.getColor()]-1];
						if(country.equals(sender))
							if(Risk.inout[indmax.getColor()]<=0&&Risk.inout[country.getColor()]>=0)
								return "movearmies " + sender.getColor() + " " + indmax.getColor() + " " + (sender.getArmies()-1);
						else
							indmax=country;
					}
				}
			}
			
			sender=indmax;
			//move from the interior (very very very very smart)
			maxfulldefended=(int)Double.NEGATIVE_INFINITY;
			for(Country country:fulldefended)
			{   double threat=threats[country.getColor()];
				if(betterdefence.contains(country))
				{   borders=new ArrayList<>();
					borders.add(country);
					FindBorders(borders,cplayer,"outer");
					int s=0;
					for(Country border:borders)
						s+=border.getArmies();
					s=s/borders.size()/2;
					//s=(int)Math.max(s/borders.size()/2,threat);
					if(country.getArmies()<s)
						continue;
				}
				if(country.getArmies()>maxfulldefended)
				{   if(betterdefence.contains(country))
					{   if(threat<6)
							threat=6;
						int n=country.getArmies()-(int)threat;
						if(n>maxfulldefended)
						{   maxfulldefended=n;
							indmax=country;
							indthreat=threat;
						}
					}
					else if(worsedefence.contains(country))
					{   int n=country.getArmies()-(int)(threat*2/3);
						if(threat<4)
							threat=4;
						if(n>maxfulldefended)
						{   maxfulldefended=n;
							indmax=country;
							indthreat=threat;
						}
					}
					else
					{   maxfulldefended=country.getArmies();
						indmax=country;
						indthreat=0;
					}
				}
			}
			if(indthreat>0&&indthreat*2<indmax.getArmies())
				indthreat=indmax.getArmies()/2;
			if((maxfulldefended>3||getReinforcements(cplayer)<6&&maxfulldefended>1)&&indmax!=null)
			{   countries=new ArrayList<>();
				List<Integer> distances=new ArrayList<>();
				Country[] from=new Country[game.getCountries().length+1];
				Country to=null;
				countries.add(indmax);
				distances.add(0);
				if(indmax.getArmies()>3||getReinforcements(cplayer)<6)
				{   if(countries.isEmpty())
						return "nomove";
					int distance=-1;
					double maxthreat=0;//Double.NEGATIVE_INFINITY;
					Country indmax1=null;
					while(true)
					{   Country country=countries.get(0);
						List<Country> neighbours=new ArrayList<>();
						HashSet<Country> incomingneighbours=new HashSet<>();
						neighbours.addAll(country.getNeighbours());
						incomingneighbours.addAll(country.getIncomingNeighbours());
						for(Country neighbour:incomingneighbours)
						{   if(neighbour.getOwner()!=cplayer)
							{   to=country;
								distance=distances.get(0);
								break;
							}
						}
						if(to!=country)
							for(Country neighbour:neighbours)
							{   if(neighbour.getOwner()!=cplayer)
								{   to=country;
									distance=distances.get(0);
									break;
								}
							}
						if(to!=country)
						{   if(distances.get(0)==0)
								for(int i=0;i<neighbours.size();i++)
								{   Country neighbour=neighbours.get(i);
									if(Risk.inout[neighbour.getColor()]<0)
									{   neighbours.remove(i);
										i--;
									}
								}
							for(Country neighbour:neighbours)
							{   if(from[neighbour.getColor()]==null)
								if((almostconquered.contains(country.getContinent())&&neighbour.getContinent()==country.getContinent())
								 ||!almostconquered.contains(country.getContinent()))
								{   countries.add(neighbour);
									distances.add(distances.get(0)+1);
									from[neighbour.getColor()]=country;
								}
							}
						}
						if(to==country)
						{   double threat;
							if(betterdefence.contains(country))
								threat=threats[country.getColor()]-country.getArmies();
							else if(worsedefence.contains(country))
								threat=threats[country.getColor()]*2/3-country.getArmies();
							else
								threat=3-country.getArmies();
							neighbours=new ArrayList<>();
							neighbours.addAll(country.getNeighbours());
							//neighbours.removeAll(country.getOwner().getTerritoriesOwned());
							neighbours=removeAll(country.getOwner(),neighbours);
							if((threat>0&&threat>maxthreat)||(threat<0&&maxthreat<=0&&threat<maxthreat&&!neighbours.isEmpty()))
							{   maxthreat=threat;
								indmax1=country;
								distance=distances.get(0);
							}
							else
							if(neighbours.isEmpty()&&maxthreat==0)
								distance=-1;
						}
						countries.remove(0);
						distances.remove(0);
						if(countries.isEmpty())
							break;
						if(distances.get(0)!=distance&&distance!=-1)
							break;
					}
					if(indmax1==null)
						return "nomove";
					Country current=indmax1;
					if(indmax==current)
						return "nomove";
					while(indmax!=from[current.getColor()])
						current=from[current.getColor()];
					if(Risk.inout[current.getColor()]<0)
						return "nomove";
					if(getReinforcements(cplayer)>=6)
						if(Risk.inout[indmax.getColor()]<=0&&Risk.inout[current.getColor()]>=0)
							if(indmax.isNeighbours(current)&&(indmax.getArmies()-Math.max((int)Math.round(indthreat),3)>0))
								return "movearmies " + indmax.getColor() + " " + current.getColor() + " " + (indmax.getArmies()-Math.max((int)Math.round(indthreat),3));
					else
						if(Risk.inout[indmax.getColor()]<=0&&Risk.inout[current.getColor()]>=0)
							if(indmax.isNeighbours(current)&&(indmax.getArmies()-Math.max((int)Math.round(indthreat),1)>0))
								return "movearmies " + indmax.getColor() + " " + current.getColor() + " " + (indmax.getArmies()-Math.max((int)Math.round(indthreat),1));
				}
			}
			return "nomove";
		}
		for (int i = 0; i < t.size(); i++) {
			Country c = t.get(i);
			if (c.getArmies() <= getMinPlacement() || gs.capitals.contains(c)) {
				continue;
			}
			//cooperation check to see if we should leave this continent
			if (c.getArmies() > 2 && gs.commonThreat != null && !c.getCrossContinentNeighbours().isEmpty() && !ownsNeighbours(c)) {
				coop: for (int j = 0; j < c.getNeighbours().size(); j++) {
					Country n = (Country)c.getNeighbours().get(j);
					if (n.getOwner() == cplayer && n.getContinent() != c.getContinent()) {
						//we have another continent to go to, ensure that the original continent is not desirable
						if (targetContinents == null) {
							List<EliminationTarget> co = findTargetContinents(gs, Collections.EMPTY_MAP, false, false);
							targetContinents = new ArrayList<>();
							for (int k = 0; k < co.size(); k++) {
								EliminationTarget et = co.get(k);
								targetContinents.add(et.co);
							}
						}
						int index = targetContinents.indexOf(c.getContinent());
						if (index == -1 && c.getContinent().getOwner() == cplayer) {
							break;
						}
						int indexOther = targetContinents.indexOf(n.getContinent());
						if ((indexOther > -1 && (index == -1 || index > indexOther)) || ((index == -1 || index > 0) && n.getContinent().getOwner() == cplayer)) {
							int toSend = c.getArmies() - getMinPlacement();
							return getMoveCommand(c, n, toSend);
						}
					}
				}
			}
			if (v.contains(c) && additionalTroopsNeeded(c, gs)/2 + getMinPlacement() >= 0) {
				continue;
			}
			filtered.add(c);
			int score = scoreCountry(c);
			for (int j = 0; j < c.getNeighbours().size(); j++) {
				Country n = (Country)c.getNeighbours().get(j);
				if (n.getOwner() != cplayer || !v.contains(n) || additionalTroopsNeeded(n, gs) < -1) {
					continue;
				}
				int total = -score + scoreCountry(n);
				if (total < lowestScore) {
					sender = c;
					receiver = n;
					lowestScore = total;
				}
			}
		}
		if (receiver != null) {
			int toSend = sender.getArmies() - getMinPlacement();
			if (v.contains(sender)) {
				toSend = -additionalTroopsNeeded(sender, gs)/2 - getMinPlacement();
			}
			return getMoveCommand(sender, receiver, toSend);
		}
		//move to the battle
		Country max = null;
		for (int i = filtered.size() - 1; i >= 0; i--) {
			Country c = filtered.get(i);
			if (!ownsNeighbours(c)) {
				filtered.remove(i);
				continue;
			}
			if (max == null || c.getArmies() > max.getArmies()) {
				max = c;
			}
			int score = scoreCountry(c);
			for (int j = 0; j < c.getNeighbours().size(); j++) {
				Country n = (Country)c.getNeighbours().get(j);
				if (n.getOwner() != cplayer || ownsNeighbours(n)) {
					continue;
				}
				int total = -score + scoreCountry(n);
				if (total < lowestScore) {
					sender = c;
					receiver = n;
					lowestScore = total;
				}
			}
		}
		if (receiver != null) {
			int toSend = sender.getArmies() - getMinPlacement();
			if (v.contains(sender)) {
				toSend = -additionalTroopsNeeded(sender, gs)/2 - getMinPlacement();
			}
			return getMoveCommand(sender, receiver, toSend);
		}
		//move from the interior (not very smart)
		if (max != null && max.getArmies() > getMinPlacement() + 1) {
			int least = Integer.MAX_VALUE;
			for (int j = 0; j < max.getNeighbours().size(); j++) {
				Country n = (Country)max.getNeighbours().get(j);
				if (max.getOwner() != cplayer) {
					continue;
				}
				if (n.getArmies() < least) {
					receiver = n;
					least = n.getArmies();
				}
			}
			if (receiver != null) {
				return getMoveCommand(max, receiver,  (max.getArmies() - getMinPlacement() - 1));
			}
		}
		return "nomove";
	}

	private String getMoveCommand(Country sender, Country receiver, int toSend)
	{       
		if(cplayer!=sender.getOwner()||cplayer!=receiver.getOwner())
			return "nomove";
		if(sender.getArmies()<toSend)
			toSend=sender.getArmies()-1;
		if(toSend>0&&sender.getNeighbours().contains(receiver))
		{   //if(Risk.inout[sender.getColor()]<=0&&Risk.inout[receiver.getColor()]>=0)
			return "movearmies " + sender.getColor() + " " + receiver.getColor() + " " + toSend;//Treba samo to.
		}
		else if(toSend<0&&receiver.getNeighbours().contains(sender))
		{   //if(Risk.inout[sender.getColor()]<=0&&Risk.inout[receiver.getColor()]>=0)
			return "movearmies " + receiver.getColor() + " " + sender.getColor() + " " + (-toSend);
		}
		return "nomove";
	}

    /**
     * Compute the battle won move.  We are just doing a quick reasoning here.
     * Ideally we would consider the full state of move all vs. move min vs. some mix.
     * @param gameState
     * @return 
     */
	protected String getBattleWon(GameState gameState) {
		if(!toattack.isEmpty()&&toattack.get(0)==game.getAttacker()&&todefend.get(0)==game.getDefender())
		{   //threats2[todefend.get(0).getColor()]=FindThreats(cplayer,todefend.get(0),todefend.get(0));
			indroll=0;
			int attackcolor=game.getAttacker().getColor();
			int defendcolor=game.getDefender().getColor();
			try{
				threats2.set(attackcolor,new ArrayList<>());
				threats2.get(attackcolor).add(0.0);
				threats2.get(attackcolor).addAll(FindThreats(cplayer,game.getAttacker()));
				threats2.set(defendcolor,new ArrayList<>());
				threats2.get(defendcolor).add(0.0);
				threats2.get(defendcolor).addAll(FindThreats(cplayer,game.getDefender()));
			}catch(Exception e)
			{
				indroll=0;
			}
			int index=game.forbiddenAttackers.indexOf(game.getAttacker());
			while(index>-1)
			{   if(index!=-1)
				{   game.forbiddenAttackers.remove(index);
					game.forbiddenAttackersTurns.remove(index);
					index=game.forbiddenAttackers.indexOf(game.getAttacker());
				}
			}
			index=game.forbiddenAttackers.indexOf(game.getDefender());
			while(index>-1)
			{   if(index!=-1)
				{   game.forbiddenAttackers.remove(index);
					game.forbiddenAttackersTurns.remove(index);
					index=game.forbiddenAttackers.indexOf(game.getDefender());
				}
			}
			index=game.previousAttackers.indexOf(game.getAttacker());
			while(index>-1)
			{   if(index!=-1)
				{   game.previousAttackers.remove(index);
					game.previousAttackersTurns.remove(index);
					game.previousAttackersTries.remove(index);
					index=game.previousAttackers.indexOf(game.getAttacker());
				}
			}
			index=game.previousAttackers.indexOf(game.getDefender());
			while(index>-1)
			{   if(index!=-1)
				{   game.previousAttackers.remove(index);
					game.previousAttackersTurns.remove(index);
					game.previousAttackersTries.remove(index);
					index=game.previousAttackers.indexOf(game.getDefender());
				}
			}
			index=game.tomoveFrom.indexOf(game.getAttacker());
			while(index>-1)
			{   if(index!=-1)
				{   game.tomoveFrom.remove(index);
					game.tomoveTo.remove(index);
					index=game.previousAttackers.indexOf(game.getAttacker());
				}
			}
			if(game.getDefender().getContinent().isOwned(cplayer))
				game.useCards2.add(game.getDefender().getContinent());

			/*betterdefence.removeAll(cplayer.getTerritoriesOwned());
			worsedefence.removeAll(cplayer.getTerritoriesOwned());
			extendedworsedefence.removeAll(cplayer.getTerritoriesOwned());
			fulldefended.removeAll(cplayer.getTerritoriesOwned());*/
			betterdefence=removeAll(cplayer,betterdefence);
			worsedefence=removeAll(cplayer,worsedefence);
			extendedworsedefence=removeAll(cplayer,extendedworsedefence);
			fulldefended=removeAll(cplayer,fulldefended);
			Player player=cplayer;
			List<Country> Betterdefence1=new ArrayList<>();
			List<Country> Worsedefence1=new ArrayList<>();
			List<Country> Borders1=new ArrayList<>();
			List<Country> Borders2=new ArrayList<>();
			List<Country> largestempire;
			Borders1.addAll(FindFullDefended(player));
			Borders2.addAll(Borders1);
			FindBorders(Borders2,player,"incoming outer");
			Borders.addAll(Borders2);
			Borders1.addAll(FindFullDefended(player));
			fulldefended.addAll(Borders1);
			if(game.smallmap==1||betterdefence.size()+worsedefence.size()>=game.getCountries().length/2)
			{   largestempire=getLargestEmpire(player);
				Borders1.removeAll(largestempire);
				Borders1.addAll(largestempire);
			}
			FindBorders(Borders1,player,"incoming outer");//vraca i negranicne teritorije, ako su susedne granicim, tj. produzenu granicu
			FindDefensible(Betterdefence1,Worsedefence1,player);
			betterdefence.addAll(Betterdefence1);
			/*if(smallmap==1)
				betterdefence.addAll(Worsedefence1);*/
			extendedworsedefence.addAll(Worsedefence1);
			extendedworsedefence.removeAll(Borders1);
			Borders1.removeAll(Worsedefence1);
			Borders1.addAll(Worsedefence1);
			Borders1.removeAll(betterdefence);
			worsedefence.addAll(Borders1);
			worsedefence.removeAll(betterdefence);
			//if(betterdefence.contains(game.getAttacker())&&!betterdefence.contains(game.getDefender()))
			//    indroll=0;
			threats[game.getAttacker().getColor()]=FindThreats(cplayer,game.getAttacker(),game.getAttacker());
			threats[game.getDefender().getColor()]=FindThreats(cplayer,game.getDefender(),game.getDefender());
			Defence=0;

			int attack=game.getAttacker().getArmies();
			int move=towinmove.get(0);
			int stay=towinstay.get(0);
			int type=attacktype.get(0);
			boolean svinajednog=game.alliance.size()+1==game.getPlayers().size() && game.alliance.contains(cplayer);
			if(stay<0)
			   stay=stay*(-1);
			if(move==2&&stay==2||move==2&&stay==3)
			{   move=attack/2;
				stay=attack-move;
				if(stay<3)
				{   move-=3-stay;
					stay=3;
				}
			}
			else
			{   if(stay==2)
					stay=3;
				if(move==2)
					move=3;
			}
			HashSet<Country> neighbours=new HashSet<>();
			neighbours.addAll(game.getDefender().getNeighbours());
			neighbours.addAll(game.getDefender().getIncomingNeighbours());
			//neighbours.removeAll(cplayer.getTerritoriesOwned());
			neighbours=removeAll(cplayer,neighbours);
			HashSet<Country> neighbours1=new HashSet<>();
			neighbours1.addAll(game.getAttacker().getNeighbours());
			neighbours1.addAll(game.getAttacker().getIncomingNeighbours());
			//neighbours.removeAll(cplayer.getTerritoriesOwned());
			neighbours1=removeAll(cplayer,neighbours1);
			//napadac je postao unutrasnja teritorija:
			if(neighbours1.isEmpty())
			{	if(betterdefence.contains(game.getAttacker()) && !svinajednog)
				{   double threat=Math.round(FindThreats(cplayer,game.getAttacker(),game.getDefender()));
					stay=(int)threat;
					if(move+stay<attack)
						move=attack-stay;
				}
			}
			//branilac je bio opkoljen:
			else if(neighbours.isEmpty())
			{   double threat=Math.round(FindThreats(cplayer,game.getDefender(),game.getDefender()));
				if(!betterdefence.contains(game.getDefender()))
					threat=threat*2/3;
				if(threat<1)
					threat=1;
				move=(int)threat;
				if(move+stay<attack)
					stay=attack-move;
			}
			if(move==0||type==-1)
				move=attack-stay;
			if(stay==0)
			{   stay=1;
				move=attack-stay;
			}
			if(move+stay>attack)
				move=attack-stay;
			else
			{   if(betterdefence.contains(game.getAttacker())
					||(almostconquered.contains(game.getAttacker().getContinent())&&!almostconquered.contains(game.getDefender().getContinent())))
					stay=attack-move;
				else
					move+=(attack-stay-move)/2;
			}
			move=Math.max(move,game.getMustMove());
			//System.out.printf("%d %d %d %d %d\n",game.getAttacker().getArmies(),move,stay,towinmove.get(0),towinstay.get(0));
			toattack.remove(0);
			todefend.remove(0);
			attacktype.remove(0);
			towinmove.remove(0);
			towinstay.remove(0);
			return "move " + move;
		}
		if (ownsNeighbours(game.getDefender())) {
			return "move " + game.getMustMove();
		}

		int minsend=-1,maxsend=-1,send;
		if(maxsend<game.getMustMove())
			maxsend=game.getMustMove();
		if(minsend<game.getMustMove())
			minsend=game.getMustMove();

		int needed = -game.getAttacker().getArmies();
		List<Country> border = getBorder(gameState);

		boolean specialCase = false;
		if (!isIncreasingSet() && !eliminating && type != PLAYER_AI_EASY) {
				/*
				 * we're not in the middle of a planned attack, so attempt to fortify on the fly
				 */
		Continent cont = null;
		if (!border.contains(game.getDefender()) || !gameState.me.owned.contains(game.getDefender().getContinent())) {
				//check if the attacker neighbours one of our continents
				for (Country c : game.getAttacker().getCrossContinentNeighbours()) {
								if (gameState.me.owned.contains(c.getContinent())) {
										cont = c.getContinent();
										specialCase = true;
										break;
								}
						}
		}
		if (border.contains(game.getAttacker())) {
				specialCase = true;
				if (cont != null && game.getCardMode() == RiskGame.CARD_FIXED_SET && border.contains(game.getDefender()) && game.getDefender().getContinent() == game.getAttacker().getContinent()) {
						cont = null;
						specialCase = false;
				} else if (gameState.me.owned.contains(game.getAttacker().getContinent())) {
						cont = game.getAttacker().getContinent();
				}
		}
		if (specialCase && game.getCardMode() != RiskGame.CARD_FIXED_SET) {
				needed = additionalTroopsNeeded(game.getAttacker(), gameState);
		}
		if (cont != null) {
				if (cont.getBorderCountries().size() > 2) {
						needed += cont.getArmyValue();
				} else {
				if (specialCase && game.getCardMode() == RiskGame.CARD_FIXED_SET) {
						needed = additionalTroopsNeeded(game.getAttacker(), gameState);
				}
						needed += (4 * cont.getArmyValue())/Math.max(1, cont.getBorderCountries().size());
				}
		} else if (specialCase) {
				needed += game.getMaxDefendDice();
			}
		}   
		if (specialCase && ((breaking != null && breaking.getOwner() != null) || gameState.commonThreat != null)) {
			needed/=2;
		}
		if (!specialCase && ownsNeighbours(game.getAttacker())) {
			send=Math.max(game.getMustMove(), game.getAttacker().getArmies() - getMinPlacement());
			if(maxsend==-1)
				maxsend=send;
			if(minsend==-1)
				minsend=send;
			return "move " + Math.min(Math.max(send,minsend),maxsend);
		}
		if (!specialCase && game.getMaxDefendDice() == 3 && !ownsNeighbours(game.getAttacker()) && gameState.me.playerValue > gameState.orderedPlayers.get(0).playerValue) {
				needed += game.getMaxDefendDice(); //make getting cards more difficult
		}
		int forwardMin = 0;
		if (game.getAttacker().getArmies() - 1 > game.getMustMove()) {
			Country defender = game.getDefender();
			HashMap<Country, AttackTarget> targets = new HashMap<>();
			searchTargets(targets, defender, game.getAttacker().getArmies() - 1, 0, 1, cplayer.getExtraArmies(), true, gameState);
			forwardMin = getMinRemaining(targets,  game.getAttacker().getArmies() - 1, border.contains(game.getAttacker()), gameState);
			if (forwardMin == Integer.MAX_VALUE) {
					return "move " + game.getMustMove();
			}
		}
			send=Math.max(Math.min(-needed, game.getAttacker().getArmies() - Math.max(getMinPlacement(), forwardMin)), game.getMustMove());
			if(maxsend==-1)
				maxsend=send;
			if(minsend==-1)
				minsend=send;
		if(cplayer.getType()==AIDomination.PLAYER_AI_AVERAGE&&game.getCardMode()==RiskGame.CARD_ITALIANLIKE_SET/*&&smallmap==0*/)
			return "move " + Math.min(Math.max(send,minsend),maxsend);
		else
			return "move " + send;
	}

    /**
     * Delay trading in cards when sensible
     * TODO: this should be more strategic, such as looking ahead for elimination
     * @return 
     */
        @Override
    public String getTrade() {
    	if (!game.getTradeCap() && type != AIDomination.PLAYER_AI_EASY) {
			if(cplayer.getType()==AIDomination.PLAYER_AI_AVERAGE&&game.getCardMode()==RiskGame.CARD_ITALIANLIKE_SET/*&&smallmap==0*/)
			{   //totrade.clear();
				try{
				while(!totrade.isEmpty())
				{   while(totrade.get(0).size()<3)
						totrade.remove(0);
					Card Cards[]=new Card[3];
					Cards[0]=totrade.get(0).get(0);
					Cards[1]=totrade.get(0).get(1);
					Cards[2]=totrade.get(0).get(2);
					totrade.remove(0);
					return super.getTrade(Cards);
				}}
				catch (Exception e){
					int i=0;
				}
				//pojacavanje ostecenih granica:
				double threat;
				List<Card> cards=new ArrayList<>();
				cards.addAll(cplayer.getCards());

				int armiesdeficit=-cplayer.getExtraArmies(),armies=0;
				if(!game.useCards1.isEmpty())
				{   List<Double> Threats=new ArrayList<>();
					for(Country country:game.useCards1)
					{   if(country.getOwner()!=cplayer)
							continue;
						if(betterdefence.contains(country)||game.previousFulldefended.get(0).contains(country.getColor()))
						{   /*if(fulldefended.contains(country))
								threats1[j]=Math.max(6,Threats[j]*1.6+2);
							else*/
							threat=Math.max(6,FindThreats(cplayer,country,country)+2);
							threat-=country.getArmies();
						}
						else
						{   
							threat=Math.max(6,FindThreats(cplayer,country,country)+2.25);
							threat=threat*2/3-country.getArmies();
						}
						if((int)threat>2+game.getCountries().length/75)
						{   armiesdeficit+=(int)threat;
							Threats.add(threat);
						}
					}
					if(armiesdeficit>0)
					{   List<List<Card>> result=FindBestTrade(game,cards,armiesdeficit);
						armies=0;
						for(List<Card> cardss:result)
						{   String s1,s2,s3;
							s1=cardss.get(0).getName();
							s2=cardss.get(1).getName();
							s3=cardss.get(2).getName();
							armies+=game.getTradeAbsValue(s1,s2,s3,2);
						}
						List<Country> Tofortify=new ArrayList<>();
						List<Integer> TofortifY=new ArrayList<>();
						List<Country> DamagedBorders=new ArrayList<>();
						DamagedBorders.addAll(game.useCards1);
						int plan2;
						try{
						plan2=RecoverBorders(armies,DamagedBorders,Threats,Tofortify,TofortifY);}
						catch(Exception e){
							plan2=0;
						}
						totrade.addAll(result);
						DodajUPlanove2(tofortify1,tofortify2,Tofortify,TofortifY);
					}
					game.useCards1.clear();
				}
				//pojacavanje ostecenih granica, 2. plan:
				else
				{   List<Double> Threats=new ArrayList<>();
					List<Country> countries=new ArrayList<>();
					countries.addAll(betterdefence);
					countries.addAll(worsedefence);
					countries=retainAll(cplayer,countries);
					countries.removeAll(fulldefended);
					countries.removeAll(extendedworsedefence);
					List<Country> DamagedBorders=new ArrayList<>();
					double Threat=0;
					for(int j=0;j<countries.size();j++)
					{   Country country=countries.get(j);
						if(betterdefence.contains(country)||game.previousFulldefended.get(0).contains(country.getColor()))
						{   /*if(fulldefended.contains(country))
								threats1[j]=Math.max(6,Threats[j]*1.6+2);
							else*/
							Threat=Math.max(6,FindThreats(cplayer,country,country)+2);
							Threat-=country.getArmies();
						}
						else
						{   
							Threat=Math.max(6,FindThreats(cplayer,country,country)+2.25);
							Threat=Threat*2/3-country.getArmies();
						}
						if((int)Threat>2+game.getCountries().length/75)
						{   armiesdeficit+=(int)Threat;
							DamagedBorders.add(country);
							Threats.add(Threat);
						}
					}
					if(armiesdeficit>0)
					{   
						List<List<Card>> result=FindBestTrade(game,cards,armiesdeficit);
						armies=0;
						try{
							for(List<Card> cardss:result)
							{   String s1,s2,s3;
								s1=cardss.get(0).getName();
								s2=cardss.get(1).getName();
								s3=cardss.get(2).getName();
								armies+=game.getTradeAbsValue(s1,s2,s3,2);
							}
						}catch(Exception e){
							armies+=0;}
						List<Country> Tofortify=new ArrayList<>();
						List<Integer> TofortifY=new ArrayList<>();
						int plan2;
						try{
						plan2=RecoverBorders(armies,DamagedBorders,Threats,Tofortify,TofortifY);}
						catch(Exception e){
							plan2=0;
						}
						game.useCards1.clear();
						totrade.addAll(result);
						DodajUPlanove2(tofortify1,tofortify2,Tofortify,TofortifY);
					}
				}
				//odbrana tek osvojenih kontinenata:
				if(!game.useCards2.isEmpty())
				{   List<Country> countries=new ArrayList<>();
					List<Double> Threats=new ArrayList<>();
					for(Continent continent:game.useCards2)
						if (continent.isOwned(cplayer))
							countries.addAll(continent.getTerritoriesContained());
					for(Country country:countries)
					{   threat=((int)threats[country.getColor()]);
						if(betterdefence.contains(country))
							if(threat>=6||country.getArmies()>=6)
								armiesdeficit+=Math.max((int)threat-country.getArmies(),0);
							else
								armiesdeficit+=6-country.getArmies();
					}
					if(armiesdeficit>0)
					{   List<List<Card>> result=FindBestTrade(game,cards,armiesdeficit);
						totrade.addAll(result);
					}
					game.useCards2.clear();
				}
				try{
				if(!totrade.isEmpty())
				{   while(totrade.get(0).size()<3)
						totrade.remove(0);
					Card Cards[]=new Card[3];
					Cards[0]=totrade.get(0).get(0);
					Cards[1]=totrade.get(0).get(1);
					Cards[2]=totrade.get(0).get(2);
					totrade.remove(0);
					return super.getTrade(Cards);
				}
				}catch(Exception e){
					int a=0;
				}
				return "endtrade";
			}
    		if (game.getCardMode() != RiskGame.CARD_ITALIANLIKE_SET && cplayer.getCards().size() >= RiskGame.DEFAULT_MAX_CARDS) {
    			return super.getTrade();
    		}
    		GameState gs = getGameState(cplayer, true);
    		if (gs.commonThreat == null && gs.orderedPlayers.size() > 1 && !pressAttack(gs) && !isTooWeak(gs)) {
    			return "endtrade";
    		}
    	}
    	return super.getTrade();
    }
    
	//plan se deli na delove
	private void plan1()
	{   int extraarmies=cplayer.getExtraArmies(),plan2=-1;
		int[] plan1={-1,-1};
				//game.forbiddenAttackers=new ArrayList<>();
				//game.forbiddenAttackersTurns=new ArrayList<>();

		List<Country> Toattack1=new ArrayList<>();
		List<Country> Todefend1=new ArrayList<>();
		List<Integer> Attacktype1=new ArrayList<>();//napadamo dok ne ostane toliko tenkova odbrani
		List<Integer> Towinmove1=new ArrayList<>();
		List<Integer> Towinstay1=new ArrayList<>();
		List<Country> Tofortify1=new ArrayList<>();
		List<Integer> TofortifY1=new ArrayList<>();

		List<Country> Tofortify2=new ArrayList<>();
		List<Integer> TofortifY2=new ArrayList<>();

		List<Country> Tofortify3=new ArrayList<>();
		List<Integer> TofortifY3=new ArrayList<>();

		Country[] countries=game.getCountries();
		HashSet<Country> neighbours=new HashSet<>();
		List<Country> ourcountries=cplayer.getTerritoriesOwned();
		for(Country country:ourcountries)
			neighbours.addAll(country.getNeighbours());
		neighbours=removeAll(cplayer,neighbours);
		if(threats2.isEmpty())
		{   threats2.add(new ArrayList<>());
			for(int i=0;i<countries.length;i++)
			{   threats2.add(new ArrayList<>());
				if(neighbours.contains(countries[i]))
					threats2.get(i+1).add(FindThreats(cplayer,countries[i],countries[i]));
				else
					threats2.get(i+1).add(0.0);
				if(countries[i].getOwner()==cplayer)
					threats2.get(i+1).addAll(FindThreats(cplayer,countries[i]));
			}
		}
		if(game.previousBorders.size()>=game.getPlayers().size())
		if(!game.previousBorders.get(game.getPlayers().size()-1).isEmpty())
		{   //vracanje probijenih granica:
			plan1=RecoverBorders(extraarmies,Toattack1,Todefend1,Attacktype1,Towinmove1,Towinstay1,Tofortify1,TofortifY1);
			extraarmies-=plan1[1];
			//ako je izgubljeno više od pola tenkova na granici:
			List<Integer> PreviousBorders=new ArrayList<>();
			List<Integer> PreviousFulldefended=new ArrayList<>();
			List<Country> DamagedBorders=new ArrayList<>();
			List<Double> Threats=new ArrayList<>();
			PreviousBorders.addAll(game.previousBorders.get(game.getPlayers().size()-1));
			PreviousBorders.addAll(game.previousFulldefended.get(game.getPlayers().size()-1));
			for(int i:PreviousBorders)
			{   Country country=game.getCountryInt(i);
				if(country.getOwner()==cplayer&&country.getArmies()*2<=game.previousArmies.get(game.getPlayers().size()-1).get(i-1))
				{   DamagedBorders.add(country);
					double threat=((int)threats[country.getColor()]);
					if(betterdefence.contains(country))
						Threats.add(threat-country.getArmies());
					else
						Threats.add(threat*2/3-country.getArmies());
				}
			}
			PreviousFulldefended.addAll(game.previousFulldefended.get(game.getPlayers().size()-1));
			for(int i:PreviousFulldefended)
			{   Country country=game.getCountryInt(i);
				if(!fulldefended.contains(country))
				{   DamagedBorders.add(country);
					double threat=((int)threats[country.getColor()]);
					if(betterdefence.contains(country))
						Threats.add(threat-country.getArmies());
					else
						Threats.add(threat*2/3-country.getArmies());
				}
			}
			if(!DamagedBorders.isEmpty())
			{   try{
				plan2=RecoverBorders(extraarmies,DamagedBorders,Threats,Tofortify2,TofortifY2);}
				catch(Exception e){
					plan2=0;
				}
				extraarmies-=plan2;
			}
		}
		//pojacavanje slabih teritorija
		FortifyWeak(extraarmies,Tofortify3,TofortifY3);
		if(!Toattack1.isEmpty()||plan2>0)
			;
		if(plan1[0]>1&&extraarmies>=2)
			DodajUPlanove1(toattack,todefend,attacktype,towinmove,towinstay,tofortify1,tofortify2,
			   Toattack1,Todefend1,Attacktype1,Towinmove1,Towinstay1,Tofortify1,TofortifY1);
		DodajUPlanove2(tofortify1,tofortify2,Tofortify2,TofortifY2);
		DodajUPlanove2(tofortify1,tofortify2,Tofortify3,TofortifY3);
	}

	private void plan2()
	{   int extraarmies=cplayer.getExtraArmies();
		List<Country> Toattack=new ArrayList<>();
		List<Country> Todefend=new ArrayList<>();
		List<Integer> Attacktype=new ArrayList<>();//napadamo dok ne ostane toliko tenkova odbrani
		List<Integer> Towinmove=new ArrayList<>();
		List<Integer> Towinstay=new ArrayList<>();
		List<Country> Tofortify=new ArrayList<>();
		List<Integer> TofortifY=new ArrayList<>();

		List<Country> Toattack3=new ArrayList<>();
		List<Country> Todefend3=new ArrayList<>();
		List<Integer> Attacktype3=new ArrayList<>();//napadamo dok ne ostane toliko tenkova odbrani
		List<Integer> Towinmove3=new ArrayList<>();
		List<Integer> Towinstay3=new ArrayList<>();
		List<Country> Tofortify3=new ArrayList<>();
		List<Integer> TofortifY3=new ArrayList<>();

		List<Country> Tofortify4=new ArrayList<>();
		List<Integer> TofortifY4=new ArrayList<>();

		Country[] countries=game.getCountries();
		HashSet<Country> neighbours=new HashSet<>();
		List<Country> ourcountries=cplayer.getTerritoriesOwned();
		for(Country country:ourcountries)
			neighbours.addAll(country.getNeighbours());
		neighbours=removeAll(cplayer,neighbours);
		if(threats2.isEmpty())
		{   threats2.add(new ArrayList<>());
			for(int i=0;i<countries.length;i++)
			{   threats2.add(new ArrayList<>());
				if(neighbours.contains(countries[i]))
					threats2.get(i+1).add(FindThreats(cplayer,countries[i],countries[i]));
				else
					threats2.get(i+1).add(0.0);
				if(countries[i].getOwner()==cplayer)
					threats2.get(i+1).addAll(FindThreats(cplayer,countries[i]));
			}
		}
		//pojacavanje teritorija bez prioriteta:
		if(extraarmies>0)
			FortifyWorsedefence(extraarmies,Tofortify4,TofortifY4);
		DodajUPlanove2(Tofortify,TofortifY,Tofortify4,TofortifY4);
		BreakBorder(extraarmies,Toattack3,Todefend3,Attacktype3,Towinmove3,Towinstay3,Tofortify3,TofortifY3);
		DodajUPlanove1(Toattack,Todefend,Attacktype,Towinmove,Towinstay,Tofortify,TofortifY,
			   Toattack3,Todefend3,Attacktype3,Towinmove3,Towinstay3,Tofortify3,TofortifY3);
		DodajUPlanove1(toattack,todefend,attacktype,towinmove,towinstay,tofortify1,tofortify2,
			   Toattack,Todefend,Attacktype,Towinmove,Towinstay,Tofortify,TofortifY);
	}

	private void plan()
	{	int extraarmies=cplayer.getExtraArmies();
		int extraarmies1,/*plan1=-1,*/plan3=-1,plan5=-1,plan7;
		int[] plan2,plan4;//prvi broj je kol'ko je vece pojacanje, a drugi kol'ko je potrebno tenkova za napad
		List<Integer> type=new ArrayList<>();
		List<Country> Toattack=new ArrayList<>();
		List<Country> Todefend=new ArrayList<>();
		List<Integer> Attacktype=new ArrayList<>();//napadamo dok ne ostane toliko tenkova odbrani
		List<Integer> Towinmove=new ArrayList<>();
		List<Integer> Towinstay=new ArrayList<>();
		List<Country> Tofortify=new ArrayList<>();
		List<Integer> TofortifY=new ArrayList<>();

		List<Country> Toattack2=new ArrayList<>();
		List<Country> Todefend2=new ArrayList<>();
		List<Integer> Attacktype2=new ArrayList<>();//napadamo dok ne ostane toliko tenkova odbrani
		List<Integer> Towinmove2=new ArrayList<>();
		List<Integer> Towinstay2=new ArrayList<>();
		List<Country> Tofortify2=new ArrayList<>();
		List<Integer> TofortifY2=new ArrayList<>();

		List<Country> Toattack4=new ArrayList<>();
		List<Country> Todefend4=new ArrayList<>();
		List<Integer> Attacktype4=new ArrayList<>();//napadamo dok ne ostane toliko tenkova odbrani
		List<Integer> Towinmove4=new ArrayList<>();
		List<Integer> Towinstay4=new ArrayList<>();
		List<Country> Tofortify4=new ArrayList<>();
		List<Integer> TofortifY4=new ArrayList<>();

		List<Country> Toattack5=new ArrayList<>();
		List<Country> Todefend5=new ArrayList<>();
		List<Integer> Attacktype5=new ArrayList<>();//napadamo dok ne ostane toliko tenkova odbrani
		List<Integer> Towinmove5=new ArrayList<>();
		List<Integer> Towinstay5=new ArrayList<>();
		List<Country> Tofortify5=new ArrayList<>();
		List<Integer> TofortifY5=new ArrayList<>();

		List<Country> Toattack6=new ArrayList<>();
		List<Country> Todefend6=new ArrayList<>();
		List<Integer> Attacktype6=new ArrayList<>();//napadamo dok ne ostane toliko tenkova odbrani
		List<Integer> Towinmove6=new ArrayList<>();
		List<Integer> Towinstay6=new ArrayList<>();
		List<Country> Tofortify6=new ArrayList<>();
		List<Integer> TofortifY6=new ArrayList<>();

		List<Country> Toattack7=new ArrayList<>();
		List<Country> Todefend7=new ArrayList<>();
		List<Integer> Attacktype7=new ArrayList<>();//napadamo dok ne ostane toliko tenkova odbrani
		List<Integer> Towinmove7=new ArrayList<>();
		List<Integer> Towinstay7=new ArrayList<>();
		List<Country> Tofortify7=new ArrayList<>();
		List<Integer> TofortifY7=new ArrayList<>();

		List<Country> Tofortify8=new ArrayList<>();
		List<Integer> TofortifY8=new ArrayList<>();

		Country[] countries=game.getCountries();
		HashSet<Country> neighbours=new HashSet<>();
		List<Country> ourcountries=cplayer.getTerritoriesOwned();
		for(Country country:ourcountries)
			neighbours.addAll(country.getNeighbours());
		neighbours=removeAll(cplayer,neighbours);
		//threats2=new ArrayList<>();
		if(threats2.isEmpty())
		{   threats2.add(new ArrayList<>());
			for(int i=0;i<countries.length;i++)
			{   threats2.add(new ArrayList<>());
				if(countries[i].getColor()==99)
					;
				if(neighbours.contains(countries[i]))
					threats2.get(i+1).add(FindThreats(cplayer,countries[i],countries[i]));
				else
					threats2.get(i+1).add(0.0);
				if(countries[i].getOwner()==cplayer)
					threats2.get(i+1).addAll(FindThreats(cplayer,countries[i]));
			}
		}

		HashSet<Country> alliedcountries=new HashSet<>();
		if(game.alliance.contains(cplayer))
		for(Player ally:game.alliance)
			if(ally!=cplayer)
			{   alliedcountries.addAll(retainAll(ally,betterdefence));
				alliedcountries.addAll(retainAll(ally,worsedefence));
				alliedcountries.addAll(retainAll(ally,fulldefended));
			}
		//napad na slabe teritorije
		plan3=AttackonWeak(extraarmies,Toattack6,Todefend6,Attacktype6,Towinmove6,Towinstay6,Tofortify6,TofortifY6);
		extraarmies-=plan3;
		//napad na kontinente:
		List<Continent> continents=new ArrayList<>();
		continents.addAll(FindContinents(extraarmies,cplayer,type));
		plan2=AttackOnContinents(continents,extraarmies,Toattack2,Todefend2,Attacktype2,Towinmove2,Towinstay2,Tofortify2,TofortifY2);
		extraarmies1=extraarmies;
		//pomeranje granica:
		List<Country> area=new ArrayList<>();
		area.addAll(Arrays.asList(game.getCountries()));
		area.removeAll(alliedcountries);
		betterdefence1=new HashSet<>();
		betterdefence1.addAll(betterdefence);
		worsedefence1=new HashSet<>();
		worsedefence1.addAll(worsedefence);
		plan4=MovingBorders(area,extraarmies,Toattack4,Todefend4,Attacktype4,Towinmove4,Towinstay4,Tofortify4,TofortifY4);
		betterdefence=new HashSet<>();
		betterdefence.addAll(betterdefence1);
		worsedefence=new HashSet<>();
		worsedefence.addAll(worsedefence1);
		plan4[1]-=extraarmies1-extraarmies;
		//sprecavanje napada na kontinente:
		if((double)game.numberofgoodplayers/game.getPlayers().size()>=0.5)
			plan5=PreventConqueringContinents(extraarmies,Toattack5,Todefend5,Attacktype5,Towinmove5,Towinstay5,Tofortify5,TofortifY5);
		else
			plan5=0;
		//skidanje kontinenata:
		plan7=BreakContinents(extraarmies,Toattack7,Todefend7,Attacktype7,Towinmove7,Towinstay7,Tofortify7,TofortifY7);
		//pojacavanje unutrasnjih teritorija:
		FortifyFulldefended(extraarmies,Tofortify8,TofortifY8);
		if(plan2[0]<0)
			plan2[0]=0;
		if(plan3<0)
			plan3=0;
		if(plan4[0]<0)
			plan4[0]=0;
		if(plan7<0)
			plan7=0;
		/*
		Najvazniji plan je onaj sa najvecim povecanjem pojacanja. U slucaju da negde ima tona tenkova, to ce biti
		Attack on continents ili Break continents, i onda oba pocinju odatle.
		1. Ako igrac nije clan alijanse, prvo ide Attack on continents.
		2. Ako su svi na jednog, prvo ide Break continents.
		3. Ako je izmedju:
			3.a. Ako ce posle osvajanja kontinenta igrac izaci iz alijanse, prvo ide Attack on continents.
			3.b. Inace, Break continents.
		Sve je u tome da li igrac treba da gleda sebe ili opste dobro.
		*/
		int[] plan=new int[3],index=new int[3];
		plan[0]=plan2[1];index[0]=2;
		plan[1]=plan4[1];index[1]=4;
		plan[2]=plan7;index[2]=8;//umesto 7, zbog zbira od 10 kasnije
		
		for(int i=0;i<plan.length-1;i++)
		{   int max=0,indmax=0;
			for(int j=i+1;j<plan.length;j++)
				if(plan[j]>max)
				{   max=plan[j];
					indmax=j;
				}
			if(plan[i]<max)
			{	int p=plan[i];
				plan[i]=plan[indmax];
				plan[indmax]=p;
				p=index[i];
				index[i]=index[indmax];
				index[indmax]=p;
			}
		}
		if(index[0]+index[1]==10 && plan2[2]==1)
			if(!game.alliance.contains(cplayer))
				DodajUPlanove1(Toattack,Todefend,Attacktype,Towinmove,Towinstay,Tofortify,TofortifY,
					   Toattack2,Todefend2,Attacktype2,Towinmove2,Towinstay2,Tofortify2,TofortifY2);
			else if(game.alliance.size()+1==game.getPlayers().size())
				DodajUPlanove1(Toattack,Todefend,Attacktype,Towinmove,Towinstay,Tofortify,TofortifY,
					   Toattack7,Todefend7,Attacktype7,Towinmove7,Towinstay7,Tofortify7,TofortifY7);
			else
			{	
				plan7+=0;
			}
		else if(index[0]==2&&plan2[2]==1)
			DodajUPlanove1(Toattack,Todefend,Attacktype,Towinmove,Towinstay,Tofortify,TofortifY,
				   Toattack2,Todefend2,Attacktype2,Towinmove2,Towinstay2,Tofortify2,TofortifY2);
		else if(index[0]==8)
			DodajUPlanove1(Toattack,Todefend,Attacktype,Towinmove,Towinstay,Tofortify,TofortifY,
				   Toattack7,Todefend7,Attacktype7,Towinmove7,Towinstay7,Tofortify7,TofortifY7);
		else
		{	DodajUPlanove1(Toattack,Todefend,Attacktype,Towinmove,Towinstay,Tofortify,TofortifY,
				   Toattack5,Todefend5,Attacktype5,Towinmove5,Towinstay5,Tofortify5,TofortifY5);
			DodajUPlanove1(Toattack,Todefend,Attacktype,Towinmove,Towinstay,Tofortify,TofortifY,
				   Toattack6,Todefend6,Attacktype6,Towinmove6,Towinstay6,Tofortify6,TofortifY6);
			for(int i=0;i<index.length;i++)
				if(index[i]==2)
					DodajUPlanove1(Toattack,Todefend,Attacktype,Towinmove,Towinstay,Tofortify,TofortifY,
						   Toattack2,Todefend2,Attacktype2,Towinmove2,Towinstay2,Tofortify2,TofortifY2);
				else if(index[i]==4)
					DodajUPlanove1(Toattack,Todefend,Attacktype,Towinmove,Towinstay,Tofortify,TofortifY,
						   Toattack4,Todefend4,Attacktype4,Towinmove4,Towinstay4,Tofortify4,TofortifY4);
				else//index[i]==8
					DodajUPlanove1(Toattack,Todefend,Attacktype,Towinmove,Towinstay,Tofortify,TofortifY,
						   Toattack7,Todefend7,Attacktype7,Towinmove7,Towinstay7,Tofortify7,TofortifY7);
			DodajUPlanove2(Tofortify,TofortifY,Tofortify8,TofortifY8);
		}
		// <editor-fold defaultstate="collapsed">
	/*	for(int i=0;i<toattack.size();i++)
		{   if(Toattack.contains(toattack.get(i))&&Todefend.contains(todefend.get(i)))
			{   toattack.remove(i);
				todefend.remove(i);
				attacktype.remove(i);
				towinmove.remove(i);
				towinstay.remove(i);
				i--;
			}
		}
		*/// </editor-fold>
		//pracenje prethodnih napada sa pojacanjem:
		if(extraarmies>0&&(game.getState()==RiskGame.STATE_ATTACKING||game.getState()==RiskGame.STATE_PLACE_ARMIES))
		{   if(!Tofortify.isEmpty())
			{   for(int i=0;i<game.forbiddenAttackers.size();i++)
				{   Country attacker=game.forbiddenAttackers.get(i);
					if(attacker.getOwner()==cplayer)
					{   game.forbiddenAttackersTurns.set(i,game.forbiddenAttackersTurns.get(i)-1);
						if(game.forbiddenAttackersTurns.get(i)==0)
						{   game.forbiddenAttackers.remove(i);
							game.forbiddenAttackersTurns.remove(i);
						}
					}
				}
			}
			int n=3;
			List<Country> countries1=TerritoriesOnDistance(cplayer.getTerritoriesOwned(),1,"max");
			countries1.removeAll(betterdefence);
			countries1.removeAll(worsedefence);
			if(countries1.isEmpty())
				n=3+game.getCountries().length/50;
			else
			{   n=3+game.getCountries().length/50;
				for(Country country:countries1)
				{   List<Country> neighbours1=removeAll(cplayer,country.getIncomingNeighbours());
					neighbours1.removeAll(game.forbiddenAttackers);
					List<Country> neighbours2=new ArrayList<>();
					neighbours2.addAll(neighbours1);
					neighbours1.retainAll(betterdefence);
					neighbours2.retainAll(worsedefence);
					if(neighbours1.isEmpty()&&neighbours2.isEmpty())
					{   n=3;
						break;
					}
				}
			}		/*	

			// <editor-fold defaultstate="collapsed">
		/*	if(game.alliance.size()+1 == game.getPlayers().capacity())
			{	List<Country> countries = removeAll(cplayer, FindFullDefended(cplayer));
				game.tomoveFrom.clear();
				game.tomoveTo.clear();
				prvapetlja:
				for(Country country:countries)
				{	List<Country> neighbours = country.getNeighbours();
					for(Country neighbour:neighbours)
					{	if(!game.alliance.contains(neighbour.getOwner()))
						{
							game.tomoveTo.add(country);
							break prvapetlja;
						}
						game.tomoveFrom.add(country);
					}
				}
			}
			*/	// </editor-fold>

			glavnapetlja:
			for(int i=0;i<game.previousAttackers.size();i++)
				if(game.previousAttackersTries.get(i)>n&&game.previousAttackersTries.get(i)>=game.previousAttackersTurns.get(i)/2+0.5)
				{   Country attacker=game.previousAttackers.get(i);
					if(attacker.getOwner()!=cplayer)
						continue;
					int Index=Toattack.indexOf(attacker);
					if(Index>=0)
					if(Todefend.get(Index).getArmies()<=3+game.getCountries().length/50)
						continue;
					game.forbiddenAttackers.add(attacker);
					game.forbiddenAttackersTurns.add(n=3+game.getCountries().length/50);
					game.previousAttackers.remove(i);
					game.previousAttackersTurns.remove(i);
					game.previousAttackersTries.remove(i);
					//premestamo visak od pretnji:
					if(attacker.getArmies()-(int)threats[attacker.getColor()]-1>0)
					{   List<Country> empire=getConnectedEmpire(attacker);
						empire.removeAll(fulldefended);
						empire.remove(attacker);
						for(Country minattacker:minattackers)
							if(empire.contains(minattacker))
							{   game.tomoveFrom.add(attacker);
								game.tomoveTo.add(minattacker);
								continue glavnapetlja;
							}
					}
				}
				else if(game.previousAttackersTurns.get(i)>=10)
				{   game.previousAttackers.remove(i);
					game.previousAttackersTurns.remove(i);
					game.previousAttackersTries.remove(i);
				}
			for(Country attacker:Tofortify)
				if(Toattack.contains(attacker))
					if(game.previousAttackers.contains(attacker))
					{   int Index=game.previousAttackers.indexOf(attacker);
						game.previousAttackersTries.set(Index,game.previousAttackersTries.get(Index)+1);
						game.previousAttackersTurns.set(Index,game.previousAttackersTurns.get(Index)+1);
					}
					else
					{   game.previousAttackers.add(attacker);
						game.previousAttackersTurns.add(0);
						game.previousAttackersTries.add(0.5);
					}
		}
		DodajUPlanove1(toattack,todefend,attacktype,towinmove,towinstay,tofortify1,tofortify2,
			   Toattack,Todefend,Attacktype,Towinmove,Towinstay,Tofortify,TofortifY);
	}

	private void DodajUPlanove1(List<Country> Toattack, List<Country> Todefend, List<Integer> Attacktype, List<Integer> Towinmove, List<Integer> Towinstay, List<Country> Tofortify, List<Integer> TofortifY,
				List<Country> Toattack1, List<Country> Todefend1, List<Integer> Attacktype1, List<Integer> Towinmove1, List<Integer> Towinstay1, List<Country> Tofortify1, List<Integer> TofortifY1)
	{	Toattack.addAll(Toattack1);
		Todefend.addAll(Todefend1);
		Attacktype.addAll(Attacktype1);
		Towinmove.addAll(Towinmove1);
		Towinstay.addAll(Towinstay1);
		Tofortify.addAll(Tofortify1);
		TofortifY.addAll(TofortifY1);
	}

	private void DodajUPlanove2(List<Country> Tofortify, List<Integer> TofortifY, List<Country> Tofortify1, List<Integer> TofortifY1)
	{	Tofortify.addAll(Tofortify1);
		TofortifY.addAll(TofortifY1);
		Tofortify1.clear();
		TofortifY1.clear();
	}

	private int[] RecoverBorders(int extraarmies,
			 List<Country> Toattack, List<Country> Todefend, List<Integer> Attacktype, List<Integer> Towinmove, List<Integer> Towinstay, List<Country> Tofortify1, List<Integer> Tofortify2)
	{   List<Integer> LostBordersColors=new ArrayList<>();
		List<Country> LostBorders=new ArrayList<>();
		int[] povratnavrednost=new int[2];
		int index=game.getPlayers().size()-1;
		LostBordersColors.addAll(game.previousFulldefended.get(index));
		for(int i:LostBordersColors)
		{   Country country=game.getCountryInt(i);
			if(country.getOwner()!=cplayer)
				LostBorders.add(country);
		}
		LostBordersColors=new ArrayList<>();
		LostBordersColors.addAll(game.previousBorders.get(index));
		for(int i:LostBordersColors)
		{   Country country=game.getCountryInt(i);
			if(country.getOwner()!=cplayer)
				LostBorders.add(country);
		}
		if(!LostBorders.isEmpty())
			povratnavrednost=MovingBorders(LostBorders,extraarmies,Toattack,Todefend,Attacktype,Towinmove,Towinstay,Tofortify1,Tofortify2);
		if(povratnavrednost[0]==0||povratnavrednost[1]>extraarmies)
		{   povratnavrednost[1]=0;
			Toattack.clear();
			Todefend.clear();
			Attacktype.clear();
			Towinmove.clear();
			Towinstay.clear();
			Tofortify1.clear();
			Tofortify2.clear();
		}
		else
			game.useCards1.addAll(Todefend);
		return povratnavrednost;
	}

	private int RecoverBorders(int extraarmies, List<Country> DamagedBorders, List<Double> Threats, List<Country> Tofortify1, List<Integer> Tofortify2)
	{   int Extraarmies=extraarmies;
		if(Threats.size()>1)
		for(int i=0;i<Threats.size()-1;i++)
		{   int ind=0;
			Country P;
			double max=0;
			for(int j=i+1;j<Threats.size();j++)
				if(Threats.get(j)>max)
				{   max=Threats.get(j);
					ind=j;
				}
			if(max==0)
				break;
			if(max>Threats.get(i))
			{   Threats.set(ind,Threats.get(i));
				Threats.set(ind,max);
				P=DamagedBorders.get(i);
				DamagedBorders.set(i,DamagedBorders.get(ind));
				DamagedBorders.set(ind,P);
			}
		}

		int ind=1;
		int index;
		while(ind==1)
		{   ind=0;
			for(int i=1;i<Threats.size();i++)
			{   Country country=DamagedBorders.get(i);
				if(fulldefended.contains(country))
					continue;
				if(Threats.get(0)/Threats.get(i)>=10&&Threats.get(i)>4&&country.getOwner()==cplayer)
				{   Threats.set(ind,Threats.get(i)-1);
					if(Tofortify1.contains(country))
					{   index=Tofortify1.indexOf(country);
						Tofortify2.set(index,Tofortify2.get(index)+1);
					}
					else
					{   Tofortify1.add(country);
						Tofortify2.add(1);
					}
					extraarmies--;
					i--;
					ind=1;
				}
				if(extraarmies==0)
					return Extraarmies;
			}
			for(int i=1;i<Threats.size();i++)
			{   Country country=DamagedBorders.get(i);
				if(fulldefended.contains(country))
					continue;
				if(Threats.size()>2)
				if(Threats.get(0)>=1&&Threats.get(i)>=Threats.get(i+1)&&country.getOwner()==cplayer)
				{   Threats.set(ind,Threats.get(i)-1);
					if(Tofortify1.contains(country))
					{   index=Tofortify1.indexOf(country);
						Tofortify2.set(index,Tofortify2.get(index)+1);
					}
					else
					{   Tofortify1.add(country);
						Tofortify2.add(1);
					}
					extraarmies--;
					i--;
					ind=1;
				}
				if(extraarmies==0)
					return Extraarmies;
			}
			Country country=DamagedBorders.get(0);
			if(!fulldefended.contains(country)&&Threats.get(0)>=1&&country.getOwner()==cplayer)
			{   Threats.set(ind,Threats.get(0)-1);
				if(Tofortify1.contains(country))
				{   index=Tofortify1.indexOf(country);
					Tofortify2.set(index,Tofortify2.get(index)+1);
				}
				else
				{   Tofortify1.add(country);
					Tofortify2.add(1);
				}
				extraarmies--;
				ind=1;
			}
		}
		game.useCards1.addAll(Tofortify1);
		return Extraarmies-extraarmies;
	}

	private int FortifyWeak(int extraarmies,List<Country> Tofortify1, List<Integer> Tofortify2)
	{   HashSet<Country> countries=new HashSet<>();
		int Extraarmies=extraarmies;
		if((double)game.numberofgoodplayers/game.getPlayers().size()<0.5)
		{   countries.addAll(fulldefended);
			countries.addAll(betterdefence);
			countries.addAll(worsedefence);
			//countries.retainAll(cplayer.getTerritoriesOwned());
			countries=retainAll(cplayer,countries);
		}
		else
			countries.addAll(cplayer.getTerritoriesOwned());
		countries.removeAll(fulldefended);
		for(Country country:countries)
		{   if(country.getArmies()==2)
			{   Tofortify1.add(country);
				Tofortify2.add(1);
				extraarmies--;
			}
			if(extraarmies==0)
				return Extraarmies;
		}
		for(Country country:countries)
		{   if(country.getArmies()<3&&!Tofortify1.contains(country))
			{   if(extraarmies>1)
				{   Tofortify1.add(country);
					Tofortify2.add(2);
					extraarmies--;
				}
				else
				{   Tofortify1.add(country);
					Tofortify2.add(1);
					extraarmies--;
				}
			}
			if(extraarmies==0)
				return Extraarmies;
		}
		return Extraarmies-extraarmies;
	}

	private int FortifyWorsedefence(int extraarmies,List<Country> Tofortify1, List<Integer> Tofortify2)
	{   int l=game.getCountries().length;
		int Extraarmies=extraarmies;
		int ind=1;
		int index;
		while(ind==1)
		{   ind=0;
			for(int i=1;i<l;i++)
			{   if(indthreats[i]==0)
					break;
				Country country=game.getCountries()[indthreats[i]-1];
				if(fulldefended.contains(country))
					continue;
				if(threats1[1]/threats1[i]>=10&&threats1[i]>4&&country.getOwner()==cplayer)
				{   threats1[i]--;
					if(Tofortify1.contains(country))
					{   index=Tofortify1.indexOf(country);
						Tofortify2.set(index,Tofortify2.get(index)+1);
					}
					else
					{   Tofortify1.add(country);
						Tofortify2.add(1);
					}
					extraarmies--;
					i--;
					ind=1;
				}
				if(extraarmies==0)
					return Extraarmies;
			}
			for(int i=1;i<l;i++)
			{   if(indthreats[i]==0)
					break;
				Country country=game.getCountries()[indthreats[i]-1];
				if(fulldefended.contains(country))
					continue;
				if(threats1[i]>=1&&threats1[i]>=threats1[i+1]&&country.getOwner()==cplayer)
				{   threats1[i]--;
					if(Tofortify1.contains(country))
					{   index=Tofortify1.indexOf(country);
						Tofortify2.set(index,Tofortify2.get(index)+1);
					}
					else
					{   Tofortify1.add(country);
						Tofortify2.add(1);
					}
					extraarmies--;
					i--;
					ind=1;
				}
				if(extraarmies==0)
					return Extraarmies;
			}
			if(indthreats[1]==0)
				break;
			Country country=game.getCountries()[indthreats[1]-1];
			if(!fulldefended.contains(country)&&threats1[1]>=1&&country.getOwner()==cplayer)
			{   threats1[1]--;
				if(Tofortify1.contains(country))
				{   index=Tofortify1.indexOf(country);
					Tofortify2.set(index,Tofortify2.get(index)+1);
				}
				else
				{   Tofortify1.add(country);
					Tofortify2.add(1);
				}
				extraarmies--;
				ind=1;
			}
		}
		return Extraarmies-extraarmies;
	}

	private int FortifyFulldefended(int extraarmies,List<Country> Tofortify1, List<Integer> Tofortify2)
	{   HashSet<Country> countries=new HashSet<>();
		int Extraarmies=extraarmies;
		if((double)game.numberofgoodplayers/game.getPlayers().size()<0.5)
		{   countries.addAll(fulldefended);
			countries.addAll(betterdefence);
			countries.addAll(worsedefence);
			//countries.retainAll(cplayer.getTerritoriesOwned());
			countries=retainAll(cplayer,countries);
		}
		else
			countries.addAll(cplayer.getTerritoriesOwned());
		int reinforcements=getReinforcements(cplayer);
		if(reinforcements>=6)
			countries.retainAll(fulldefended);
		else
			return 0;
		//necemo pojacavati unutrasnje teritorije ako je neprijatelj daleko da bismo brze napredovali:
		List<Country> countries1=new ArrayList<>();
		countries1.addAll(countries);
		countries=new HashSet<>();
		prvapetlja:
		while(!countries1.isEmpty())
		{   Country country=countries1.get(0);
			List<Country> countries2=getConnectedEmpire(country);
			countries1.removeAll(countries2);
			List<Country> countries3=TerritoriesOnDistance(countries2,2+game.getCountries().length/100,"all");
			countries3=removeAll(cplayer,countries3);//bliski neprijatelji
			countries2.retainAll(fulldefended);//unutrasnje teritorije oko country
			for(Country country3:countries3)
				if(country3.getArmies()>5)
				{   countries.addAll(countries2);
					continue prvapetlja;
				}
		}
		for(Country country:countries)
		{   if(country.getArmies()==2)
			{   Tofortify1.add(country);
				Tofortify2.add(1);
				extraarmies--;
			}
			if(extraarmies==0)
				return Extraarmies;
		}
		for(Country country:countries)
		{   if(country.getArmies()<3&&!Tofortify1.contains(country))
			{   if(extraarmies>1)
				{   Tofortify1.add(country);
					Tofortify2.add(2);
					extraarmies--;
				}
				else
				{   Tofortify1.add(country);
					Tofortify2.add(1);
					extraarmies--;
				}
			}
			if(extraarmies==0)
				return Extraarmies;
		}
		return Extraarmies-extraarmies;
	}

	private int AttackonWeak(int extraarmies,
			 List<Country> Toattack, List<Country> Todefend, List<Integer> Attacktype, List<Integer> Towinmove, List<Integer> Towinstay, List<Country> Tofortify1, List<Integer> Tofortify2)
	{   int i,j,n,N,todefendlength=0;
		int Extraarmies=extraarmies;
		int minstay;
		//List<Country> betterdefence,worsedefence;
		//betterdefence=new HashSet<>();
		//worsedefence=new HashSet<>();
		List<Country> countries1=new ArrayList<>();
		List<Integer> countries1starts=new ArrayList<>();
		countries1.addAll(cplayer.getTerritoriesOwned());
		//FindDefensible(betterdefence,worsedefence,cplayer);
		HashSet<Country> alliedcountries=new HashSet<>();
		if(game.alliance.contains(cplayer))
		for(Player ally:game.alliance)
			if(ally!=cplayer)
			{   alliedcountries.addAll(retainAll(ally,betterdefence));
				alliedcountries.addAll(retainAll(ally,worsedefence));
				alliedcountries.addAll(retainAll(ally,fulldefended));
			}
		for(i=0;i<countries1.size();i++)
		{   Country country=countries1.get(i);
			int ind=0;
			HashSet<Country> neighbours=new HashSet<>();
			neighbours.addAll(country.getNeighbours());
			//neighbours.removeAll(cplayer.getTerritoriesOwned());
			neighbours=removeAll(cplayer,neighbours);
			for(Country neighbour:neighbours)
				if(neighbour.getArmies()<3 && !alliedcountries.contains(neighbour))
				{   ind=1;
					break;
				}
			if(ind==0)
			{   countries1.remove(i);
				i--;
			}
		}
		//ako ima teritorija u koje ne moramo nista da dodajemo
		List<Integer> restofthreats=new ArrayList<>();
		for(i=0;i<countries1.size();i++)
		{   Country country=countries1.get(i);
			int Restofthreats=countries1.get(i).getArmies();
			if(betterdefence.contains(country))
				//Restofthreats-=Math.round(FindThreats(cplayer,country,null)*3/4);
				Restofthreats-=Math.round(threats[country.getColor()]);
			else if(almostconquered.contains(country.getContinent()))
				Restofthreats-=Math.max(Math.round(threats[country.getColor()])*2/3,6);
			else if(worsedefence.contains(country)&&!extendedworsedefence.contains(country))
				Restofthreats-=Math.round(threats[country.getColor()])*2/3;
			else
				Restofthreats-=3;
			if(Restofthreats<3||country.getArmies()<6)
			{   countries1.remove(country);
				i--;
			}
			else
				restofthreats.add(Restofthreats);
		}
		for(i=0;i<countries1.size();i++)
			countries1starts.add(i);
		for(i=0;i<countries1.size();i++)
		{   Country country=countries1.get(i);
			if(restofthreats.get(countries1starts.get(i))<3)
				continue;
			double maxthreat=Double.POSITIVE_INFINITY;//0
			int Countries1starts;
			HashSet<Country> neighbours=new HashSet<>();
			neighbours.addAll(country.getNeighbours());
			//neighbours.removeAll(cplayer.getTerritoriesOwned());
			neighbours=removeAll(cplayer,neighbours);
			Country country1=null,country2=null;
			for(Country neighbour:neighbours)
			{   //double threat=FindThreats(cplayer,neighbour,null);
				double threat=threats[neighbour.getColor()];
				if(neighbour.getArmies()==1&&threat<maxthreat&&3-restofthreats.get(countries1starts.get(i))<=0)//>maxthreat
					if(!Todefend.contains(neighbour)&&cplayer!=neighbour.getOwner()&&!alliedcountries.contains(neighbour))
					{   country1=country;
						country2=neighbour;
						maxthreat=threat;
					}
			}
			if(country1!=null&&!Toattack.contains(country1))
			{   Toattack.add(country1);
				Todefend.add(country2);
				countries1.add(country2);
				Countries1starts=countries1starts.get(countries1.indexOf(country1));
				countries1starts.add(Countries1starts);
				Attacktype.add(-1);
				Towinmove.add(3);
				minstay=3;
				HashSet<Country> neighbors=new HashSet<>();
				neighbors.addAll(country1.getIncomingNeighbours());
				//neighbors.removeAll(cplayer.getTerritoriesOwned());
				neighbors=removeAll(cplayer,neighbors);
				neighbors.removeAll(Toattack);
				if(neighbors.isEmpty())
				{   minstay=1;
					neighbors.addAll(country1.getNeighbours());
					//neighbors.removeAll(cplayer.getTerritoriesOwned());
					neighbors=removeAll(cplayer,neighbors);
					neighbors.removeAll(Toattack);
					neighbors.removeAll(Todefend);
					if(neighbors.isEmpty())
						minstay=0;
				}
				if(betterdefence.contains(country)||worsedefence.contains(country)||almostconquered.contains(country.getContinent()))
					Towinstay.add(Math.max(country1.getArmies()-restofthreats.get(Countries1starts),minstay));
				else
					Towinstay.add(minstay);
				restofthreats.set(Countries1starts,restofthreats.get(Countries1starts)-3);
				int index;
				while(Todefend.contains(country1))
				{   index=Todefend.indexOf(country1);
					country1=Toattack.get(index);
					Towinmove.set(index, Towinmove.get(index)+3);
				}
				i--;
			}
		}
		for(i=0;i<countries1.size();i++)
		{   Country country=countries1.get(i);
			if(restofthreats.get(countries1starts.get(i))<3)
				continue;
			double maxthreat=Double.POSITIVE_INFINITY;//0
			int Countries1starts;
			HashSet<Country> neighbours=new HashSet<>();
			neighbours.addAll(country.getNeighbours());
			//neighbours.removeAll(cplayer.getTerritoriesOwned());
			neighbours=removeAll(cplayer,neighbours);
			Country country1=null,country2=null;
			for(Country neighbour:neighbours)
			{   //double threat=FindThreats(cplayer,neighbour,null);
				double threat=threats[neighbour.getColor()];
				if(neighbour.getArmies()<3&&threat<maxthreat&&3-restofthreats.get(countries1starts.get(i))+neighbour.getArmies()-1<=0)//>maxthreat
					if(!Todefend.contains(neighbour)&&cplayer!=neighbour.getOwner()&&!alliedcountries.contains(neighbour))
					{   country1=country;
						country2=neighbour;
						maxthreat=threat;
					}
			}
			if(country1!=null&&!Toattack.contains(country1))
			{   Toattack.add(country1);
				Todefend.add(country2);
				countries1.add(country2);
				Countries1starts=countries1starts.get(countries1.indexOf(country1));
				countries1starts.add(Countries1starts);
				Attacktype.add(-1);
				Towinmove.add(3/*+country2.getArmies()-1*/);
				minstay=3;
				HashSet<Country> neighbors=new HashSet<>();
				neighbors.addAll(country1.getIncomingNeighbours());
				//neighbors.removeAll(cplayer.getTerritoriesOwned());
				neighbors=removeAll(cplayer,neighbors);
				neighbors.removeAll(Toattack);
				if(neighbors.isEmpty())
				{   minstay=1;
					neighbors.addAll(country1.getNeighbours());
					//neighbors.removeAll(cplayer.getTerritoriesOwned());
					neighbors=removeAll(cplayer,neighbors);
					neighbors.removeAll(Toattack);
					neighbors.removeAll(Todefend);
					if(neighbors.isEmpty())
						minstay=0;
				}
				if(betterdefence.contains(country)||worsedefence.contains(country)||almostconquered.contains(country.getContinent()))
					Towinstay.add(Math.max(country1.getArmies()-restofthreats.get(Countries1starts),minstay));
				else
					Towinstay.add(minstay);
				restofthreats.set(Countries1starts,restofthreats.get(Countries1starts)-3-country2.getArmies()+1);
				int index;
				while(Todefend.contains(country1))
				{   index=Todefend.indexOf(country1);
					country1=Toattack.get(index);
					Towinmove.set(index, Towinmove.get(index)+3+country2.getArmies()-1);
				}
				i--;
			}
		}
		//ako ima teritorija tako da moramo da dodamo manje od maksimuma (3 ili 4)
		List<Country> countries=new ArrayList<>();
		countries.addAll(cplayer.getTerritoriesOwned());
		for(Country country:countries)
		{   int Restofthreats=country.getArmies();
			if(betterdefence.contains(country))
				//Restofthreats-=Math.round(FindThreats(cplayer,country,null)*3/4);
				Restofthreats-=Math.round(threats[country.getColor()]);
			else if(almostconquered.contains(country.getContinent()))
				Restofthreats-=Math.max(Math.round(threats[country.getColor()])*2/3,6);
			else if(worsedefence.contains(country))
				Restofthreats-=Math.round(threats[country.getColor()])*2/3;
			else
				Restofthreats-=3;
			if(Restofthreats<=0)
				continue;
			double maxthreat=Double.POSITIVE_INFINITY;//0
			HashSet<Country> neighbours;
			Country country1=null,country2=null;
			neighbours=new HashSet<>();
			neighbours.addAll(country.getNeighbours());
			//neighbours.removeAll(cplayer.getTerritoriesOwned());
			neighbours=removeAll(cplayer,neighbours);
			for(Country neighbour:neighbours)
			{   //double threat=FindThreats(cplayer,neighbour,null);
				double threat=threats[neighbour.getColor()];
				if(neighbour.getArmies()==1&&threat<maxthreat&&3-Restofthreats<=extraarmies)//>maxthreat
					if(!Todefend.contains(neighbour)&&cplayer!=neighbour.getOwner()&&!alliedcountries.contains(neighbour))
					{   country1=country;
						country2=neighbour;
						maxthreat=threat;
					}
			}
			if(country1!=null&&!Toattack.contains(country1))
			{   Toattack.add(country1);
				Todefend.add(country2);
				Attacktype.add(-1);
				Towinmove.add(3);
				minstay=3;
				HashSet<Country> neighbors=new HashSet<>();
				neighbors.addAll(country1.getIncomingNeighbours());
				//neighbors.removeAll(cplayer.getTerritoriesOwned());
				neighbors=removeAll(cplayer,neighbors);
				neighbors.removeAll(Toattack);
				if(neighbors.isEmpty())
				{   minstay=1;
					neighbors.addAll(country1.getNeighbours());
					//neighbors.removeAll(cplayer.getTerritoriesOwned());
					neighbors=removeAll(cplayer,neighbors);
					neighbors.removeAll(Toattack);
					neighbors.removeAll(Todefend);
					if(neighbors.isEmpty())
						minstay=0;
				}
				if(betterdefence.contains(country)||worsedefence.contains(country)||almostconquered.contains(country.getContinent()))
					Towinstay.add(Math.max(country1.getArmies()-Restofthreats,minstay));
				else
					Towinstay.add(minstay);
				Tofortify1.add(country1);
				Tofortify2.add(Math.max(3-Restofthreats,0));
				extraarmies-=Math.max(3-Restofthreats,0);
			}
		}
		for(Country country:countries)
		{   int Restofthreats=country.getArmies();
			if(betterdefence.contains(country))
				//Restofthreats-=Math.round(FindThreats(cplayer,country,null)*3/4);
				Restofthreats-=Math.round(threats[country.getColor()]);
			else if(almostconquered.contains(country.getContinent()))
				Restofthreats-=Math.max(Math.round(threats[country.getColor()])*2/3,6);
			else if(worsedefence.contains(country))
				Restofthreats-=Math.round(threats[country.getColor()])*2/3;
			else
				Restofthreats-=3;
			if(Restofthreats<=0)
				continue;
			double maxthreat=10000;//0
			HashSet<Country> neighbours;
			Country country1=null,country2=null;
			neighbours=new HashSet<>();
			neighbours.addAll(country.getNeighbours());
			//neighbours.removeAll(cplayer.getTerritoriesOwned());
			neighbours=removeAll(cplayer,neighbours);
			for(Country neighbour:neighbours)
			{   //double threat=FindThreats(cplayer,neighbour,null);
				double threat=threats[neighbour.getColor()];
				if(neighbour.getArmies()<3&&threat<maxthreat&&3-Restofthreats+neighbour.getArmies()-1<=extraarmies)//>maxthreat
					if(!Todefend.contains(neighbour)&&cplayer!=neighbour.getOwner()&&!alliedcountries.contains(neighbour))
					{   country1=country;
						country2=neighbour;
						maxthreat=threat;
					}
			}
			if(country1!=null&&!Toattack.contains(country1))
			{   Toattack.add(country1);
				Todefend.add(country2);
				Attacktype.add(-1);
				Towinmove.add(3/*+country2.getArmies()-1*/);
				minstay=3;
				HashSet<Country> neighbors=new HashSet<>();
				neighbors.addAll(country1.getIncomingNeighbours());
				//neighbors.removeAll(cplayer.getTerritoriesOwned());
				neighbors=removeAll(cplayer,neighbors);
				neighbors.removeAll(Toattack);
				if(neighbors.isEmpty())
				{   minstay=1;
					neighbors.addAll(country1.getNeighbours());
					//neighbors.removeAll(cplayer.getTerritoriesOwned());
					neighbors=removeAll(cplayer,neighbors);
					neighbors.removeAll(Toattack);
					neighbors.removeAll(Todefend);
					if(neighbors.isEmpty())
						minstay=0;
				}
				if(betterdefence.contains(country)||worsedefence.contains(country)||almostconquered.contains(country.getContinent()))
					Towinstay.add(Math.max(country1.getArmies()-Restofthreats,minstay));
				else
					Towinstay.add(minstay);
				Tofortify1.add(country1);
				Tofortify2.add(Math.max(3+country2.getArmies()-1-Restofthreats,0));
				extraarmies-=Math.max(3+country2.getArmies()-1-Restofthreats,0);
			}
		}
		//ostalo
		while(extraarmies>=3)
		{   HashSet<Country> Countries=new HashSet<>();
			List<Country> neighbours=new ArrayList<>();
			//HashSet<Country> from=new HashSet<>();
			Countries.addAll(cplayer.getTerritoriesOwned());
			//from.addAll(countries);
			Countries.addAll(todefend);
			for(Country country:Countries)
			{   HashSet<Country> neighbourss=new HashSet<>();
				neighbourss.addAll(country.getNeighbours());
				//neighbourss.removeAll(cplayer.getTerritoriesOwned());
				neighbourss=removeAll(cplayer,neighbourss);
				for(Country neighbour:neighbourss)
					if(!neighbours.contains(neighbour)&&!countries1.contains(neighbour)&&neighbour.getArmies()<3)
						neighbours.add(neighbour);
			}
			//trazimo slabe susede sa najvecim pretnjama, zatim sortiramo po broju tenkova (1 pa 2), pa po pretnjama
			//double[] threats;
			//threats=FindThreats(Arrays.asList(game.getCountries()),Arrays.asList(game.getCountries()),cplayer);
			n=neighbours.size();
			for(i=0;i<n-1;i++)
			{   int ind=0;
				Country P;
				if(neighbours.get(i).getArmies()==1)
					continue;
				for(j=i+1;j<n;j++)
					if(neighbours.get(j).getArmies()==1)
						ind=j;
				if(ind==0)
					break;
				{   P=neighbours.get(ind);
					neighbours.set(ind,neighbours.get(i));
					neighbours.set(i,P);
				}
			}
			for(i=n-1;i>=0;i--)
				if(neighbours.get(i).getArmies()==1)
					break;
			N=i+1;
			for(i=0;i<N-1;i++)
			{   int ind=0;
				double max=0;
				Country P;
				for(j=i+1;j<N;j++)
					if(threats[neighbours.get(j).getColor()]>max)
					{   max=threats[neighbours.get(j).getColor()];
						ind=j;
					}
				if(max==0)
					break;
				if(max>threats[neighbours.get(i).getColor()])
				{   P=neighbours.get(ind);
					neighbours.set(ind,neighbours.get(i));
					neighbours.set(i,P);
				}
			}
			for(i=N;i<n-1;i++)
			{   int ind=0;
				double max=10000;//0
				Country P;
				for(j=i+1;j<n;j++)
					if(threats[neighbours.get(j).getColor()]<max)//>max
					{   max=threats[neighbours.get(j).getColor()];
						ind=j;
					}
				if(max==0)
					break;
				if(max>threats[neighbours.get(i).getColor()])
				{   P=neighbours.get(ind);
					neighbours.set(ind,neighbours.get(i));
					neighbours.set(i,P);
				}
			}
			//gledamo sta cemo da napadnemo i odakle.
			for(Country neighbour:neighbours)
			{   HashSet<Country> Neighbours=new HashSet<>();
				Neighbours.addAll(neighbour.getIncomingNeighbours());
				Country country1=null,country2=null;
				int max=0;
				for(Country Neighbour:Neighbours)
					if(Neighbour.getOwner()==cplayer)
					{   max=3;
						country1=Neighbour;
						country2=Neighbour;
						break;
					}
					else if(Todefend.contains(Neighbour))
					{   country1=Neighbour;
						int index;
						while(Todefend.contains(Neighbour))
						{   index=Todefend.indexOf(Neighbour);
							Neighbour=Toattack.get(index);
							Towinmove.set(index, Towinmove.get(index)+3+neighbour.getArmies()-1);
						}
						country2=Neighbour;
						break;
					}
				if(max>0)
				{   if(extraarmies>=3+neighbour.getArmies()-1&&!Toattack.contains(country1))
					{   Toattack.add(country1);
						Todefend.add(neighbour);
						Attacktype.add(-1);
						Towinmove.add(3);
						minstay=3;
						HashSet<Country> neighbors=new HashSet<>();
						neighbors.addAll(country1.getIncomingNeighbours());
						//neighbors.removeAll(cplayer.getTerritoriesOwned());
						neighbors=removeAll(cplayer,neighbors);
						neighbors.removeAll(Toattack);
						if(neighbors.isEmpty())
						{   minstay=1;
							neighbors.addAll(country1.getNeighbours());
							//neighbors.removeAll(cplayer.getTerritoriesOwned());
							neighbors=removeAll(cplayer,neighbors);
							neighbors.removeAll(Toattack);
							neighbors.removeAll(Todefend);
							if(neighbors.isEmpty())
								minstay=0;
						}
						Towinstay.add(minstay);
						Tofortify1.add(country2);
						Tofortify2.add(3+neighbour.getArmies()-1);
						extraarmies-=3+neighbour.getArmies()-1;
					}/*
					else
					{   tofortify1.add(country2);
						tofortify2.add(extraarmies);
						extraarmies=0;
						break;
					}*/
					if(extraarmies==0)
						break;
				}
			}
			if(Todefend.size()>todefendlength)
				todefendlength=Todefend.size();
			else
				break;
		}
		return Extraarmies-extraarmies;
	}

	private void BreakBorder(int extraarmies,
			 List<Country> Toattack, List<Country> Todefend, List<Integer> Attacktype, List<Integer> Towinmove, List<Integer> Towinstay, List<Country> Tofortify1, List<Integer> Tofortify2)
	{   int i;
		List<Country> Fulldefended=new ArrayList<>();
		List<List<Country>> areas=new ArrayList<>();
		Fulldefended.addAll(fulldefended);
		Fulldefended=removeAll(cplayer,Fulldefended);
		if(game.alliance.contains(cplayer))
			for(Player ally:game.alliance)
				Fulldefended=removeAll(ally,Fulldefended);
		List<Country> itterator;
		while(!Fulldefended.isEmpty())
		{   itterator=new ArrayList<>();
			itterator.add(Fulldefended.get(0));
			Fulldefended.remove(0);
			for(i=0;i<itterator.size();i++)
			{   Country country=itterator.get(i);
				List<Country> Neighbours=country.getNeighbours();
				for(Country Neighbour:Neighbours)
					if(!itterator.contains(Neighbour)&&Fulldefended.contains(Neighbour))
					{   itterator.add(Neighbour);
						Fulldefended.remove(Neighbour);
					}
			}
			if(itterator.size()>=4)
				areas.add(itterator);
		}
		List<Country> countries=new ArrayList<>();
		boolean svinajednog=game.alliance.size()+1==game.getPlayers().size() && game.alliance.contains(cplayer);
		int[] from=new int[game.getCountries().length+1];
		double[] armiesleft=new double[game.getCountries().length+1];
		for(i=1;i<=game.getCountries().length;i++)
			if(!fulldefended.contains(game.getCountryInt(i)))
				armiesleft[i]=3;
		countries.addAll(cplayer.getTerritoriesOwned());
		countries.removeAll(fulldefended);
		for(Country country:countries)
		{   double threat=FindThreats(cplayer,country,country);
			if(betterdefence.contains(country)&&country.getArmies()-threat>0&&!svinajednog)
				armiesleft[country.getColor()]=country.getArmies()-threat+extraarmies;
			else if(worsedefence.contains(country)&&!extendedworsedefence.contains(country)&&!svinajednog)
				armiesleft[country.getColor()]=country.getArmies()-threat*2.0/3+extraarmies;
			else
				armiesleft[country.getColor()]=country.getArmies()-3.0+extraarmies;
			if(armiesleft[country.getColor()]<0)
				armiesleft[country.getColor()]=0;
		}
		//pulsiranjem odredjujemo dokle cemo stici i sa koliko tenkova:
		for(i=0;i<countries.size();i++)
		{   Country country=countries.get(i);
			List<Country> neighbours=country.getNeighbours();
			for(Country neighbour:neighbours)
			{   if(neighbour.getOwner()!=cplayer&&!fulldefended.contains(neighbour))
				if(armiesleft[country.getColor()]-3-(neighbour.getArmies()-1)*1.8>armiesleft[neighbour.getColor()])
					if(almostconquered.contains(country.getContinent())&&neighbour.getOwner()==almostconqueredP.get(almostconquered.indexOf(country.getContinent()))&&!extendedworsedefence.contains(neighbour))
					{   double threat=FindThreats(cplayer,country,country);
						if(armiesleft[country.getColor()]-threat-3-(neighbour.getArmies()-1)*1.8>3)
						{   countries.add(neighbour);
							from[neighbour.getColor()]=country.getColor();
							armiesleft[neighbour.getColor()]=armiesleft[country.getColor()]-3-(neighbour.getArmies()-1)*1.8;
						}
					}
					else
					{   countries.add(neighbour);
						from[neighbour.getColor()]=country.getColor();
						armiesleft[neighbour.getColor()]=armiesleft[country.getColor()]-3-(neighbour.getArmies()-1)*1.8;
					}
			}
		}
		int[] plan=new int[areas.size()];
		int bestplan=0;
		List<List<Country>> paths=new ArrayList<>();
		List<Country>[] toattack1=new ArrayList[areas.size()];
		List<Country>[] todefend1=new ArrayList[areas.size()];
		List<Integer>[] attacktype1=new ArrayList[areas.size()];
		List<Integer>[] towinmove1=new ArrayList[areas.size()];
		List<Integer>[] towinstay1=new ArrayList[areas.size()];
		for(int j=0;j<areas.size();j++)
		{   //trazimo najbolju putanju do granice:
			List<Country> area=areas.get(j);
			area=TerritoriesOnDistance(area,1,"all");
			List<Country> path=new ArrayList<>();
			double max=0;
			Country Max=null;
			for(Country country:area)
			{   if(countries.contains(country))
				if(armiesleft[country.getColor()]>max)
				{   max=armiesleft[country.getColor()];
					Max=country;
				}
			}
			path.add(Max);
			paths.add(path);
			if(Max==null)
				continue;
			while(path.get(0).getOwner()!=cplayer)
			{   int index=from[path.get(0).getColor()];
				if(index<=0||index>game.getCountries().length)
					break;
				path.add(0,game.getCountryInt(index));
			}
			//prosirujemo oblast na slabije teritorije:
			double average=0;
			for(Country country:(List<Country>)(area.get(0).getOwner().getTerritoriesOwned()))
				average+=country.getArmies();
			average=average/area.get(0).getOwner().getTerritoriesOwned().size();
			int ind=1;
			while(ind==1)
			{   List<Country> Countries=area.get(0).getOwner().getTerritoriesOwned();
				ind=0;
				for(Country country:Countries)
					if(area.get(0).getOwner()==country.getOwner()&&!area.contains(country)&&country.getArmies()<average)
					{   area.add(country);
						ind=1;
					}
			}
			//gledamo sta cemo da napadnemo:
			List<Country> neighbours=new ArrayList<>();
			neighbours.addAll(Max.getNeighbours());
			neighbours.retainAll(fulldefended);
			neighbours.retainAll(area);
			for(Country neighbour:neighbours)
				from[neighbour.getColor()]=Max.getColor();
			double Armiesleft=armiesleft[Max.getColor()];
			while(!neighbours.isEmpty())
			{   double minneighbour=Double.POSITIVE_INFINITY;
				double mincontinent=Double.POSITIVE_INFINITY;
				double minarmies=Double.POSITIVE_INFINITY;
				Country Min=null;
				for(Country neighbour:neighbours)
				{   List<Country> Neighbours=new ArrayList<>();
					Neighbours.addAll(neighbour.getIncomingNeighbours());
					double max1=0;
					for(Country Neighbour:Neighbours)
						if(Neighbour.getArmies()>max1)
							max1=Neighbour.getArmies();
					if(neighbour.getContinent().isOwned(neighbour.getOwner())&&neighbour.getContinent().getArmyValue()>mincontinent)
					{   mincontinent=neighbour.getContinent().getArmyValue();
						minneighbour=max1;
						minarmies=neighbour.getArmies();
						Min=neighbour;
					}
					else if((neighbour.getContinent().isOwned(neighbour.getOwner())&&neighbour.getContinent().getArmyValue()==mincontinent&&max1<minneighbour)||
							max1<minneighbour)
					{   minneighbour=max1;
						minarmies=neighbour.getArmies();
						Min=neighbour;
					}
					else if(max1==minneighbour&&neighbour.getArmies()<minarmies)
					{   minneighbour=max1;
						minarmies=neighbour.getArmies();
						Min=neighbour;
					}
				}
				Country neighbour=Min;
				Country attacker=game.getCountryInt(from[neighbour.getColor()]);
				if(neighbour.getOwner()!=cplayer)
					if(Armiesleft>=(neighbour.getArmies()-1)*1.8+6)
					{   if(toattack1[j]==null)
						{   toattack1[j]=new ArrayList<>();
							todefend1[j]=new ArrayList<>();
							attacktype1[j]=new ArrayList<>();
							towinmove1[j]=new ArrayList<>();
							towinstay1[j]=new ArrayList<>();
						}
						toattack1[j].add(attacker);
						todefend1[j].add(neighbour);
						attacktype1[j].add(-2);
						towinmove1[j].add(0);
						towinstay1[j].add(3);
						while(todefend1[j].contains(attacker))
						{   int index=todefend1[j].indexOf(attacker);
							attacker=toattack1[j].get(index);
							towinmove1[j].set(index, towinmove1[j].get(index)+3+(int)((neighbour.getArmies()-1)*1.8));
							//towinstay1[j].set(index, towinstay1[j].get(index)-3-(int)((neighbour.getArmies()-1)*1.8));
						}
						plan[j]++;
						Armiesleft-=3+(int)((neighbour.getArmies()-1)*1.8);
						HashSet<Country> Neighbours=new HashSet<>();
						Neighbours.addAll(neighbour.getNeighbours());
						for(Country Neighbour:Neighbours)
							if(fulldefended.contains(Neighbour)&&!todefend1[j].contains(Neighbour)&&!neighbours.contains(Neighbour))
							{   neighbours.add(Neighbour);
								from[Neighbour.getColor()]=neighbour.getColor();
							}
					}
				neighbours.remove(neighbour);
			}
			if(plan[j]>plan[bestplan])
				bestplan=j;
		}
		if(paths.size()<=bestplan||plan[bestplan]<2+game.getCountries().length/100/**/)
			return;
		//upisivanje putanje u napad:
		List<Country> path=paths.get(bestplan);
		for(i=0;i<path.size()-1;i++)
		{   Toattack.add(path.get(i));
			Todefend.add(path.get(i+1));
			Attacktype.add(0);
			Towinmove.add(0);
			Towinstay.add(3);
		}
		Toattack.addAll(toattack1[bestplan]);
		Todefend.addAll(todefend1[bestplan]);
		Attacktype.addAll(attacktype1[bestplan]);
		Towinmove.addAll(towinmove1[bestplan]);
		Towinstay.addAll(towinstay1[bestplan]);
		Tofortify1.add(paths.get(bestplan).get(paths.get(bestplan).size()-1));
		Tofortify2.add(extraarmies);
	}

	List<List<Country>> FindSurrounded()
	{   int i,j;
		List<Country> countries=new ArrayList<>();
		List<Country> enemies=new ArrayList<>();
		List<List<Country>> surrounded=new ArrayList<>();
		countries.addAll(cplayer.getTerritoriesOwned());
		prvapetlja:
		for(Country country:countries)
		{   List<Country> neighbours=country.getNeighbours();
			for(Country neighbour:neighbours)
				if(!enemies.contains(neighbour)&&neighbour.getOwner()!=cplayer)
				{   enemies.add(neighbour);
					break prvapetlja;
				}
		}
		for(i=0;i<enemies.size();i++)
		{   Country enemy=enemies.get(i);
			List<Country> neighbours=enemy.getNeighbours();
			for(Country neighbour:neighbours)
				if(!enemies.contains(neighbour)&&neighbour.getOwner()!=cplayer)
					enemies.add(neighbour);
		}
		if(countries.size()+enemies.size()<game.getCountries().length)
		{   //ima opkoljenih teritorija
			j=0;
			List<Country> neighbours=TerritoriesOnDistance(countries,1,"max");
			List<Country> surritterator;
			while(!neighbours.isEmpty())
			{   surrounded.add(new ArrayList<>());
				surritterator=surrounded.get(j);
				surritterator.add(neighbours.get(0));
				neighbours.remove(0);
				for(i=0;i<surritterator.size();i++)
				{   Country country=surritterator.get(i);
					List<Country> Neighbours=country.getNeighbours();
					for(Country Neighbour:Neighbours)
						if(!surritterator.contains(Neighbour)&&Neighbour.getOwner()!=cplayer)
						{   surritterator.add(Neighbour);
							if(neighbours.contains(Neighbour))
								neighbours.remove(Neighbour);
						}
				}
				j++;
			}
			for(j=0;j<surrounded.size();j++)
			{   surritterator=surrounded.get(j);
				int defencearmies=0,attackarmies=0;
				for(Country country:surritterator)
					if(country.getOwner()!=cplayer)
						defencearmies+=(country.getArmies()-1)*1.5+1;
				List<Country> Countries=TerritoriesOnDistance(surritterator,1,"max");
				for(Country country:Countries)
					if(country.getOwner()==cplayer)
						attackarmies+=country.getArmies();
				attackarmies+=cplayer.getExtraArmies();
				if(attackarmies<defencearmies)
					surrounded.remove(surritterator);
			}
			//Lista listi surrounded su sve opkoljene oblasti koje mozda mozemo da osvojimo.
		}
		return surrounded;
	}

	HashSet<Continent> FindContinents(int extraarmies,Player player,List<Integer> type)
	{   Continent[] continents=game.getContinents();
		//List<Country> Toattack=new ArrayList<>();
		//List<Country> Todefend=new ArrayList<>();
	//	long time1,time2,time3,time4;
		type.clear();
		double attack=0;
		//double[] paths=FindPaths(player);
		List<Double> parameter=new ArrayList<>();
		HashSet<Continent> areas=new HashSet<>();
		List<Continent> Continents=new ArrayList<>();
		int minreinforcementsneed=(int)Double.POSITIVE_INFINITY,indmin=0;
		prvapetlja:
		for(int j=0;j<continents.length;j++,attack=0)
		{   Continent continent=continents[j];
			//	time1=System.nanoTime();
			//kol'ko treba da se osvoji kontinent
			int reinforcementsneed;
			if(continent.isOwned(player))
				continue;
			if(continent.getArmyValue()==0)
				continue;
			//ne napadamo kontinente pored kojih/u kojima nemamo bar 1 teritoriju:
			//to vise ne vazi!
			List<Country> territories = new ArrayList<>();
			int ind=0;
			// <editor-fold defaultstate="collapsed">
		/*	territories=TerritoriesOnDistance(continent.getTerritoriesContained(),1,"all");
			for(Country country:territories)
				if(country.getOwner()==player)
				{   ind=1;
					break;
				}
			if(ind==0)
				continue;
			territories.clear();*/
			// </editor-fold>
			
		/*	u napad racunamo najbolju od udaljenih teritorija pod nekim od uslova:
			1. svi na jednog
			2. ako je teritorija granicna i ne cuva kontinent, ako je dobitak kontinenta veci od gubitka
			3. inace, samo ostatak od pretnje
		*/
			String Type="standard";
			if(game.alliance.size()+1==game.getPlayers().size() && game.alliance.contains(cplayer))
				Type="alliance";
			//poslednje 3 liste su povratne
			List<Country> sources = new ArrayList<>();
			List<Country> netreba = new ArrayList<>();
			List<Double> maxarmiesleft = new ArrayList<>();
			FindPathsToContinent(cplayer, continent, Type, sources, null, maxarmiesleft);
			for(double armies:maxarmiesleft)
				attack+=armies;
			
			territories.clear();
			territories.addAll(continent.getTerritoriesContained());
			HashSet<Country> territories2=new HashSet<>();
			for(Country country:territories)
			{   if(country.getOwner()!=player)
					attack-=(country.getArmies()-1)*1.8;
				else 
				{   HashSet<Country> neighbours1=new HashSet<>();
					neighbours1.addAll(country.getNeighbours());
					neighbours1.addAll(country.getIncomingNeighbours());
					//neighbours1.retainAll(continent.getTerritoriesContained());
					neighbours1=retainAll(continent,neighbours1);
					//neighbours1.removeAll(player.getTerritoriesOwned());
					neighbours1=removeAll(player,neighbours1);
					if(!neighbours1.isEmpty())
						attack+=Math.max(country.getArmies()-3,0);
				}
			}
			//u napadace racunamo i susede kontinenta ako mogu da napadnu samo kontinent ili ako nisu granica:
			territories=TerritoriesOnDistance(continent.getTerritoriesContained(),1,"max");
			territories2.addAll(territories);
			territories2=retainAll(player,territories2);
			int n;
			for(Country country:territories2)
			{   HashSet<Country> neighbours=new HashSet<>();
				neighbours.addAll(country.getNeighbours());
				//neighbours.removeAll(player.getTerritoriesOwned());
				neighbours=removeAll(player,neighbours);
				//neighbours.retainAll(continent.getTerritoriesContained());
				neighbours=retainAll(continent,neighbours);
				if(!neighbours.isEmpty())
				if(betterdefence.contains(country)||(worsedefence.contains(country)&&!extendedworsedefence.contains(country)))
				{   if(!betterdefence.contains(country))
						n=(int)Math.round(country.getArmies()-FindThreats(player,country,country))*2/3;
					else
						n=(int)Math.round(country.getArmies()-FindThreats(player,country,country));
					//double p=country.getArmies()-3-n;
					if(n>0)
						attack+=Math.max(n,0);
				}
				else
					attack+=Math.max(country.getArmies()-3,0);
			}
			//if(attack+extraarmies<0)
			//    continue;
			
			List<Country> from;
			List<Country> to;
			HashSet<Country> borders1=new HashSet<>();//na kontinentu
			HashSet<Country> borders2=new HashSet<>();//van koninenta
			territories.clear();
			territories.addAll(continent.getTerritoriesContained());
			to=TerritoriesOnDistance(territories,-1,"max");
			borders1.addAll(continent.getIncomingBorderCountries());
			borders2.addAll(to);
			to.clear();
			to.addAll(continent.getIncomingBorderCountries());
			from=TerritoriesOnDistance(to,-4-game.getCountries().length/100,"all");
			from=removeAll(continent,from);
			double threats[]=new double[game.getCountries().length+1];
			if(!from.isEmpty())
				threats=FindThreats(from,to,player);
			//pretanjama van kontienta dodelimo maskimalnu pretnju susedu na kontinentu:
			//kako je kljucno da nijedne dve teritorije na kontinentu nemaju istu pretnju,
			//dodaje se veoma sitan razlomak koji ce odigrati ulogu u slucaju jednakosti dve pretnje:
			for(Country country:borders1)
			{   HashSet<Country> neighbours=new HashSet<>();
				neighbours.addAll(country.getIncomingNeighbours());
				neighbours.retainAll(borders2);
				threats[country.getColor()]+=(double)country.getColor()/100000000;
				for(Country neighbour:neighbours)
					if(threats[country.getColor()]>threats[neighbour.getColor()])
						threats[neighbour.getColor()]=threats[country.getColor()];
			}
			//izbacujemo skoro sve duplikate (i tamo gde su manje) pretnji tako da dobijemo minimalnu kolicinu:
			for(Country country:borders1)
			{   HashSet<Country> neighbours=new HashSet<>();
				neighbours.addAll(country.getIncomingNeighbours());
				neighbours.retainAll(borders2);
				ind=0;
				for(Country neighbour:neighbours)
					if(threats[country.getColor()]>=threats[neighbour.getColor()])
						ind=1;
				if(ind==0)
					threats[country.getColor()]=0;
			}
			for(Country country:borders1)
				if(threats[country.getColor()]!=0)
					threats[country.getColor()]-=(double)country.getColor()/100000000;
			for(Country country:borders2)
				threats[country.getColor()]=0;
			for(int i=1;i<=game.getCountries().length;i++)
				attack-=threats[i];
			reinforcementsneed=(int)Math.round(-attack);
			if(reinforcementsneed<0)
				reinforcementsneed=0;
			if(reinforcementsneed<minreinforcementsneed)
			{   minreinforcementsneed=reinforcementsneed;
				indmin=j;
			}
			if(reinforcementsneed>extraarmies)
				continue;
			Continents.add(continent);
			//parametar za sortiranje:
			territories=new ArrayList<>();
			territories.addAll(continent.getIncomingBorderCountries());
			//territories.removeAll(player.getTerritoriesOwned());
			territories=removeAll(player,territories);
			//territories.removeAll(continent.getTerritoriesContained());
			territories=removeAll(continent,territories);
			for(int i=0;i<territories.size();i++)
			{   Country country=territories.get(i);
				HashSet<Country> neighbours=new HashSet<>();
				neighbours.addAll(country.getIncomingNeighbours());
				for(Country neighbour:neighbours)
					territories.remove(neighbour);
			}
			parameter.add((double)continent.getArmyValue()/(territories.size()+1)+1/(reinforcementsneed+1));
		}
		//sortiraneje po parametru:
		double max,p;
		int indmax=0;
		Continent continent;
		//System.out.printf("k %d %d\n",Continents.size(),parameter.size());
		for(int i=0;i<Continents.size()-1;i++)
		{   max=0;
			for(int j=i+1;j<Continents.size();j++)
			{   if(parameter.get(j)>max)
				{   max=parameter.get(j);
					indmax=j;
				}
			}
			if(max<parameter.get(i))
			{   continent=Continents.get(i);
				Continents.set(i,Continents.get(indmax));
				Continents.set(indmax,continent);
				p=parameter.get(i);
				parameter.set(i,parameter.get(indmax));
				parameter.set(indmax,p);
			}
		}
		for(Continent Continent1:Continents)
			areas.add(Continent1);
		//Ako ne mozemo da osvojimo nijedan kontinent, pokusacemo da ga osvojimo iz vise poteza, a namericemo se za kontinent koji se najlakse osvaja:
		if(areas.isEmpty())
		{   areas.add(continents[indmin]);
			type.add(0);
		}
		else
			type.add(1);
		return areas;
	}

	HashSet<Continent> FindContinents2(int extraarmies,Player player,List<Integer> type,int[] armies)
	{   Continent[] continents=game.getContinents();
		//List<Country> Toattack=new ArrayList<>();
		//List<Country> Todefend=new ArrayList<>();
		type.clear();
		double attack;
		//double[] paths=FindPaths(player);
		List<Double> parameter=new ArrayList<>();
		HashSet<Continent> areas=new HashSet<>();
		List<Continent> Continents=new ArrayList<>();
		int minreinforcementsneed=(int)Double.POSITIVE_INFINITY,indmin=0;
		for(int j=0;j<continents.length;j++)
		{   Continent continent=continents[j];
			//kol'ko treba da se osvoji kontinent
			int reinforcementsneed;
			if(continent.isOwned(player))
				continue;
			if(continent.getArmyValue()==0)
				continue;
			//ne napadamo kontinente pored kojih/u kojima nemamo bar 1 teritoriju:
			List<Country> territories=TerritoriesOnDistance(continent.getTerritoriesContained(),1,"all");
			//territories.retainAll(player.getTerritoriesOwned());
			territories=retainAll(player,territories);
			if(territories.isEmpty())
				continue;
			territories.clear();
			List<Country> territories1;
			HashSet<Country> territories2=new HashSet<>();
			territories.addAll(continent.getTerritoriesContained());
			attack=0;
			for(Country country:territories)
			{   if(country.getOwner()!=player)
					attack-=(Math.max(armies[country.getColor()]-1,0))*1.8;
				else 
				{   HashSet<Country> neighbours1=new HashSet<>();
					neighbours1.addAll(country.getNeighbours());
					neighbours1.addAll(country.getIncomingNeighbours());
					//neighbours1.retainAll(continent.getTerritoriesContained());
					neighbours1=retainAll(continent,neighbours1);
					//neighbours1.removeAll(player.getTerritoriesOwned());
					neighbours1=removeAll(player,neighbours1);
					if(!neighbours1.isEmpty())
						attack+=Math.max(armies[country.getColor()]-3,0);
				}
			}
			//u napadace racunamo i susede kontinenta ako mogu da napadnu samo kontinent ili ako nisu granica:
			territories=new ArrayList<>();
			territories1=TerritoriesOnDistance(continent.getTerritoriesContained(),1,"max");
			territories2.addAll(territories1);
			//territories2.retainAll(player.getTerritoriesOwned());
			territories2=retainAll(player,territories2);
			territories.addAll(territories2);
			for(Country country:territories)
			{   HashSet<Country> neighbours=new HashSet<>();
				neighbours.addAll(country.getNeighbours());
				//neighbours.removeAll(player.getTerritoriesOwned());
				neighbours=removeAll(player,neighbours);
				//neighbours.retainAll(continent.getTerritoriesContained());
				neighbours=retainAll(continent,neighbours);
				if(!neighbours.isEmpty())
				if(betterdefence.contains(country)||worsedefence.contains(country))
				{   int n;
					if(!betterdefence.contains(country))
						n=(int)Math.round(armies[country.getColor()]-FindThreats(player,country,country))*2/3;
					else
						n=(int)Math.round(armies[country.getColor()]-FindThreats(player,country,country));
					//double p=armies[country.getColor()]-3-n;
					if(n>0)
						attack+=Math.max(n,0);
				}
				else
					attack+=Math.max(armies[country.getColor()]-3,0);
			}
			if(attack+extraarmies<0)
				continue;

			List<Country> from;
			List<Country> to;
			HashSet<Country> borders1=new HashSet<>();//na kontinentu
			HashSet<Country> borders2=new HashSet<>();//van koninenta
			territories.clear();
			territories.addAll(continent.getTerritoriesContained());
			to=TerritoriesOnDistance(territories,-1,"max");
			borders1.addAll(continent.getIncomingBorderCountries());
			borders2.addAll(to);
			to.clear();
			to.addAll(continent.getIncomingBorderCountries());
			from=TerritoriesOnDistance(to,-4-game.getCountries().length/100,"all");
			from=removeAll(continent,from);
			double threats[]=new double[game.getCountries().length+1];
			if(!from.isEmpty())
				threats=FindThreats(from,to,player);
			//pretanjama van kontienta dodelimo maskimalnu pretnju susedu na kontinentu:
			//kako je kljucno da nijedne dve teritorije na kontinentu nemaju istu pretnju,
			//dodaje se veoma sitan razlomak koji ce odigrati ulogu u slucaju jednakosti dve pretnje:
			for(Country country:borders1)
			{   HashSet<Country> neighbours=new HashSet<>();
				neighbours.addAll(country.getIncomingNeighbours());
				neighbours.retainAll(borders2);
				threats[country.getColor()]+=(double)country.getColor()/100000000;
				for(Country neighbour:neighbours)
					if(threats[country.getColor()]>threats[neighbour.getColor()])
						threats[neighbour.getColor()]=threats[country.getColor()];
			}
			//izbacujemo skoro sve duplikate (i tamo gde su manje) pretnji tako da dobijemo minimalnu kolicinu:
			for(Country country:borders1)
			{   HashSet<Country> neighbours=new HashSet<>();
				neighbours.addAll(country.getIncomingNeighbours());
				neighbours.retainAll(borders2);
				int ind=0;
				for(Country neighbour:neighbours)
					if(threats[country.getColor()]>=threats[neighbour.getColor()])
						ind=1;
				if(ind==0)
					threats[country.getColor()]=0;
			}
			for(Country country:borders1)
				if(threats[country.getColor()]!=0)
					threats[country.getColor()]-=(double)country.getColor()/100000000;
			for(Country country:borders2)
				threats[country.getColor()]=0;
			for(int i=1;i<=game.getCountries().length;i++)
				attack-=threats[i];
			reinforcementsneed=(int)Math.round(-attack);
			if(reinforcementsneed<0)
				reinforcementsneed=0;
			if(reinforcementsneed<minreinforcementsneed)
			{   minreinforcementsneed=reinforcementsneed;
				indmin=j;
			}
			if(reinforcementsneed>extraarmies)
				continue;
			Continents.add(continent);
			//parametar za sortiranje:
			territories=new ArrayList<>();
			territories.addAll(continent.getIncomingBorderCountries());
			for(int i=0;i<territories.size();i++)
			{   Country country=territories.get(i);
				HashSet<Country> neighbours=new HashSet<>();
				neighbours.addAll(country.getIncomingNeighbours());
				//neighbours.removeAll(player.getTerritoriesOwned());
				neighbours=removeAll(player,neighbours);
				//neighbours.removeAll(continent.getTerritoriesContained());
				neighbours=removeAll(continent,neighbours);
				if(neighbours.isEmpty())
				{   territories.remove(country);
					i--;
				}
			}
			parameter.add((double)continent.getArmyValue()/(territories.size()+1));
		}
		//sortiraneje po parametru:
		double max,p;
		int indmax=0;
		Continent continent;
		//System.out.printf("k %d %d\n",Continents.size(),parameter.size());
		for(int i=0;i<Continents.size()-1;i++)
		{   max=0;
			for(int j=i+1;j<Continents.size();j++)
			{   if(parameter.get(j)>max)
				{   max=parameter.get(j);
					indmax=j;
				}
			}
			if(max<parameter.get(i))
			{   continent=Continents.get(i);
				Continents.set(i,Continents.get(indmax));
				Continents.set(indmax,continent);
				p=parameter.get(i);
				parameter.set(i,parameter.get(indmax));
				parameter.set(indmax,p);
			}
		}
		for(Continent Continent1:Continents)
			areas.add(Continent1);
		//Ako ne mozemo da osvojimo nijedan kontinent, pokusacemo da ga osvojimo iz vise poteza, a namericemo se za kontinent koji se najlakse osvaja:
		if(areas.isEmpty())
		{   areas.add(continents[indmin]);
			type.add(0);
		}
		else
			type.add(1);
		return areas;
	}

	private int[] AttackOnContinents(List<Continent> continents, int extraarmies,
			 List<Country> Toattack, List<Country> Todefend, List<Integer> Attacktype, List<Integer> Towinmove, List<Integer> Towinstay, List<Country> Tofortify1, List<Integer> Tofortify2)
	{   int i;
		int[] povratnavrednost;
		int[] Povratnavrednost=new int[3];
		List<Country> Toattack1,Todefend1,Tofortify11;
		List<Integer> Attacktype1,Towinmove1,Towinstay1,Tofortify21;
		List<Country> area=new ArrayList<>();
		HashSet<Country> alliedcountries=new HashSet<>();
		if(game.alliance.contains(cplayer))
			for(Player ally:game.alliance)
				if(ally!=cplayer)
				{   alliedcountries.addAll(retainAll(ally,betterdefence));
					alliedcountries.addAll(retainAll(ally,worsedefence));
					alliedcountries.addAll(retainAll(ally,fulldefended));
				}
		for(i=0;i<continents.size();i++)
		{   Toattack1=new ArrayList<>();
			Todefend1=new ArrayList<>();
			Attacktype1=new ArrayList<>();
			Towinmove1=new ArrayList<>();
			Towinstay1=new ArrayList<>();
			Tofortify11=new ArrayList<>();
			Tofortify21=new ArrayList<>();
			Continent continent=continents.get(i);
			
			//kopiramo trenutne vlasnike i broj tenkova teritorija da bismo gledali unapred, a posle cemo da vratimo:
			List<Player> owners=new ArrayList<>();
			List<Player> players=new ArrayList<>();
			players.addAll(game.getPlayers());
			int armies[]=new int[game.getCountries().length];
			for(i=0;i<game.getCountries().length;i++)
			{   owners.add(game.getCountries()[i].getOwner());
				armies[i]=game.getCountries()[i].getArmies();
			}
			
			int p=game.getPlayers().size();
			double[] countriesnumber1=new double[p];
			double[] countriesnumber2=new double[p];
			for(i=0;i<p;i++)
				countriesnumber1[i]=((Player)game.getPlayers().get(i)).getTerritoriesOwned().size();
			
			//ako se napad pocinje sa vece udaljenosti od kontinenta:
			if(Toattack.isEmpty())
			{	String Type="standard";
				boolean svinajednog=game.alliance.size()+1==game.getPlayers().size() && game.alliance.contains(cplayer);
				if(svinajednog)
					Type="alliance";
				List<Country> from = new ArrayList<>();
				List<Country> to = new ArrayList<>();
				int n=game.getCountries().length+1;
				List<Double> maxarmiesleft = new ArrayList<>();
				double[] paths = FindPathsToContinent(cplayer, continent, Type, from, to, maxarmiesleft);
				//U prvoj iteraciji se samo dodje do ivice kontinenta, a u sledecoj se osvaja kontinent.
				while(!to.isEmpty())
				{   Country To=to.get(0);
					List<Country> path = new ArrayList<>();
					path.add(To);
					while(To!=from.get(0))
					{	To=game.getCountryInt((int)paths[n+To.getColor()]);
						path.add(0,To);
					}
					from.remove(0);
					to.remove(0);

					Country defender=path.get(1);
					Country attacker=path.get(0);
					double threat=FindThreats(cplayer,attacker,attacker);
					if(threat<0)
						threat=0;
					if(worsedefence.contains(attacker))
					{   if(extendedworsedefence.contains(attacker))
							threat=0;
						else
							threat=threat*2/3;
					}
					else if(almostconquered.contains(attacker.getContinent())&&svinajednog)
						threat=threat*2/3;
					else if(!betterdefence.contains(attacker))
						threat=0;
					threat=Math.max(threat,3);
					Tofortify1.add(attacker);
					Tofortify2.add(extraarmies);
					while(true)
					{	Toattack.add(attacker);
						Todefend.add(defender);
						Attacktype.add(-1);
						Towinmove.add(0);
						Towinstay.add((int)Math.round(threat));
						if(threat>1)
							threat=1;
						path.remove(0);
						if(path.size()<2)
							break;
						
						double attack=attacker.getArmies()-(defender.getArmies()-1)*1.8+1;
						int stay=(int)threat;
						int move=(int)(attack-stay);
						move=Math.max(move,3);
						attacker.removeArmies(attacker.getArmies());
						attacker.addArmies(stay);
						defender.removeArmies(defender.getArmies());
						defender.addArmies(move);
						defender.getOwner().getTerritoriesOwned().remove(defender);
						defender.setOwner(cplayer);
						cplayer.getTerritoriesOwned().add(defender);
						
						attacker=defender;
						defender=path.get(1);
					}
					Povratnavrednost[0]=extraarmies;
					Povratnavrednost[1]+=continent.getArmyValue();
					Povratnavrednost[2]=1;
				}
			}
			area.addAll(continent.getTerritoriesContained());
			HashSet<Country> alliedcountries1=new HashSet<>();
			alliedcountries1.addAll(area);
			alliedcountries1.retainAll(alliedcountries);
			if(!alliedcountries1.isEmpty())
				continue;
			betterdefence1=new HashSet<>();
			betterdefence1.addAll(betterdefence);
			worsedefence1=new HashSet<>();
			worsedefence1.addAll(worsedefence);
			povratnavrednost=MovingBorders(area,extraarmies,Toattack1,Todefend1,Attacktype1,Towinmove1,Towinstay1,Tofortify11,Tofortify21);
			betterdefence=new HashSet<>();
			betterdefence.addAll(betterdefence1);
			worsedefence=new HashSet<>();
			worsedefence.addAll(worsedefence1);
			int Reinforcements=povratnavrednost[0];
			area.clear();
			area.addAll(continent.getTerritoriesContained());
			area.removeAll(Todefend1);
			//area.removeAll(cplayer.getTerritoriesOwned());
			area=removeAll(cplayer,area);
			if(extraarmies-Reinforcements<0)
				break;
			extraarmies-=Reinforcements;
			DodajUPlanove1(Toattack,Todefend,Attacktype,Towinmove,Towinstay,Tofortify1,Tofortify2,
				   Toattack1,Todefend1,Attacktype1,Towinmove1,Towinstay1,Tofortify11,Tofortify21);
			if(povratnavrednost[0]>0)
				Povratnavrednost[0]+=povratnavrednost[0];
			Povratnavrednost[1]+=povratnavrednost[1];
			if(area.isEmpty())
			   Povratnavrednost[1]+=continent.getArmyValue();
			
			//vracanje izmenjenih podataka o teritorijama na staro:
			for(i=0;i<game.getCountries().length;i++)
			{   Country country=game.getCountries()[i];
				int Armies=armies[i];
				country.getOwner().getTerritoriesOwned().remove(country);
				country.setOwner(owners.get(i));
				owners.get(i).getTerritoriesOwned().add(country);
				country.removeArmies(country.getArmies());
				country.addArmies(Armies);
			}
			game.getPlayers().clear();
			game.getPlayers().addAll(players);
			
			for(i=0;i<p;i++)
				countriesnumber2[i]=((Player)game.getPlayers().get(i)).getTerritoriesOwned().size();
			for(i=0;i<p;i++)
				if(countriesnumber1[i]!=countriesnumber2[i])
					i+=0;
		}
		// <editor-fold defaultstate="collapsed">
		//Ako ne mozemo da osvojimo nijedan kontinent, pokusacemo da ga osvojimo iz vise poteza, a namericemo se na kontinent koji se najlakse osvaja:
	/*	if(Toattack.isEmpty()&&!continents.isEmpty())
		{   Toattack1=new ArrayList<>();
			Todefend1=new ArrayList<>();
			Attacktype1=new ArrayList<>();
			Towinmove1=new ArrayList<>();
			Towinstay1=new ArrayList<>();
			Tofortify11=new ArrayList<>();
			Tofortify21=new ArrayList<>();
			betterdefence1=new HashSet<>();
			betterdefence1.addAll(betterdefence);
			worsedefence1=new HashSet<>();
			worsedefence1.addAll(worsedefence);
			povratnavrednost=MovingBorders(continents.get(0).getTerritoriesContained(),extraarmies,Toattack1,Todefend1,Attacktype1,Towinmove1,Towinstay1,Tofortify11,Tofortify21);
			betterdefence=new HashSet<>();
			betterdefence.addAll(betterdefence1);
			worsedefence=new HashSet<>();
			worsedefence.addAll(worsedefence1);
			DodajUPlanove1(Toattack,Todefend,Attacktype,Towinmove,Towinstay,Tofortify1,Tofortify2,
				   Toattack1,Todefend1,Attacktype1,Towinmove1,Towinstay1,Tofortify11,Tofortify21);
			if(povratnavrednost[0]>0)
				Povratnavrednost[0]+=povratnavrednost[0];
			Povratnavrednost[1]+=povratnavrednost[1];
			Povratnavrednost[2]=0;
		}*/
		// </editor-fold>
		return Povratnavrednost;
	}

	private int PreventConqueringContinents(int extraarmies,
			 List<Country> Toattack, List<Country> Todefend, List<Integer> Attacktype, List<Integer> Towinmove, List<Integer> Towinstay, List<Country> Tofortify1, List<Integer> Tofortify2)
	{   int i,j,max,sum,Sum,min,indmax=0,indweak=0,reinforcementprevented=0;
		List<Integer> type=new ArrayList<>();
		List<Player> players=game.getPlayers();
		HashSet<Continent> toremove=new HashSet<>();
		//Ima li na karti previse malih kontinenata?
		double averagevalue=0,averagesize=0;
		int count=0;
		for(Continent continent:game.getContinents())
			if(continent.getTerritoriesContained().size()>1)
			{   averagevalue+=continent.getArmyValue();
				averagesize+=continent.getTerritoriesContained().size();
				count++;
			}
		averagevalue=averagevalue/count;
		averagesize=averagesize/count;
		if(averagesize<4.5)
			for(Continent continent:game.getContinents())
				if(continent.getArmyValue()<averagevalue+2)
					toremove.add(continent);
		if(toremove.size()==game.getContinents().length)
			return 0;
		Continent[] allcontinents=game.getContinents();
		//koji igrac moze da osvoji koji kontinent:
		int[][] matrix=new int[allcontinents.length][players.size()];
		int[] index=new int[allcontinents.length];
		int[] vulnerability=new int[allcontinents.length];//ugrozenost kontinenata
		for(i=0;i<allcontinents.length;i++)
			index[i]=i;
		for(i=0;i<allcontinents.length;i++)
			vulnerability[i]=1;
		//Da li je igrac slab?
		int e=getReinforcements(cplayer);
		max=e;sum=0;Sum=0;min=e;
		for(Player player:players)
			if(player!=cplayer)
			{   int n=getReinforcements(player);
				Sum+=n;
				if(n>max)
					max=n;
				if(n>=e*4/3&&n>=e+2)
					sum++;
				if(n<min)
					min=n;
			}
		if(max>=2*e&&e<=(int)min*4/3&&sum*2>=game.getPlayers().size())
		{   indweak=1;
			if(e*(players.size()-1)<Sum)
			{   indweak=2;
				return 0;
			}
		}

		int numberofhumans=0;
		for(i=0;i<players.size();i++)
		{   Player player=players.get(i);
			if(player.getType()==5)
				numberofhumans++;
		}
		for(i=0;i<players.size();i++)
		{   Player player=players.get(i);
			if(game.alliance.contains(player))
				continue;
			//Ako su bar trecina ljudi, necemo sabotirati druge kompjutere
			if(numberofhumans>1&&player.getType()==4)
				continue;
			if(player==cplayer)
				continue;
			HashSet<Continent> continents=new HashSet<>();
			//kontinenti koje igrac moze da osvoji:
			continents.addAll(FindContinents(getReinforcements(player),player,type));
			if(type.get(0)==1)
				for(Continent continent:continents)
					matrix[continent.id][i]=1;
			//kontinenti kojih igrac drzi bar 2/3, a nama je ostala jos jedna teritorija:
			for(Continent continent:allcontinents)
			{   HashSet<Country> countries=new HashSet<>();
				HashSet<Country> ourcountries=new HashSet<>();
				countries.addAll(continent.getTerritoriesContained());
				//countries.retainAll(player.getTerritoriesOwned());
				countries=retainAll(player,countries);
				ourcountries.addAll(cplayer.getTerritoriesOwned());
				//ourcountries.retainAll(continent.getTerritoriesContained());
				ourcountries=retainAll(continent,ourcountries);
				if(ourcountries.size()>=1&&countries.size()*3>=(continent.getTerritoriesContained().size()-1)*2)
					matrix[continent.id][i]=1;
			}
		}
		for(Continent continent:allcontinents)
		{   HashSet<Country> countries=new HashSet<>();
			countries.addAll(continent.getTerritoriesContained());
			for(i=0;i<players.size();i++)
				if(matrix[continent.id][i]==1)
					countries=removeAll((Player)game.getPlayers().get(i),countries);
			for(Country country:countries)
				vulnerability[continent.id]+=Math.max(country.getArmies()-3,0);
		}
		//sortiranje matrice po vrednosti/ugrozenost kontinenata:
		int[] p;
		int P;
		for(i=0;i<allcontinents.length-1;i++)
		{   max=0;
			for(j=i+1;j<allcontinents.length;j++)
				if((allcontinents[index[j]].getArmyValue())/vulnerability[index[j]]>max)
				{   max=(allcontinents[index[j]].getArmyValue())/vulnerability[index[j]];
					indmax=j;
				}
			if((allcontinents[index[i]].getArmyValue())/vulnerability[index[i]]<max)
			{   p=matrix[indmax];
				matrix[indmax]=matrix[i];
				matrix[i]=p;
				P=index[indmax];
				index[indmax]=index[i];
				index[i]=P;
			}
		}
		Continent[] continents=allcontinents;
		Tofortify1.clear();
		Tofortify2.clear();
		//pojacavanje odbrane kontinenta:
		for(i=0;i<continents.length;i++)
		{   sum=0;
			for(j=0;j<players.size();j++)
				sum+=matrix[i][j];
			if(sum==0)
				continue;
			Continent continent=allcontinents[index[i]];
			if(toremove.contains(continent))
				continue;
			//List<Country> countries=new ArrayList<>();
			List<Country> ourcountries=new ArrayList<>();
			//max=0;
			double threat;
			ourcountries.addAll(cplayer.getTerritoriesOwned());
			//ourcountries.retainAll(continent.getTerritoriesContained());
			ourcountries=retainAll(continent,ourcountries);
			if(ourcountries.isEmpty())
				continue;
			// <editor-fold defaultstate="collapsed">
			/*for(Country country:ourcountries)
				if(country.getArmies()>max)
				{   max=country.getArmies();
					if(!Tofortify1.isEmpty())
						Tofortify1.remove(Tofortify1.size()-1);
					//Tofortify1.add(country);
				}*/
			/*for(j=0;j<players.size();j++)
				if(matrix[i][j]==1)
				{   countries.add(ourcountries.get(0));
					countries=TerritoriesOnDistance(countries,-4-game.getCountries().length/50,"all");
					//countries.retainAll(players.get(j).getTerritoriesOwned());
					countries=retainAll(players.get(j),countries);

				}*/
			// </editor-fold>
			if(indweak==0)
				Tofortify1.add(ourcountries.get(0));
			else
			{   int Index=almostconquered.indexOf(continent);
				if(Index!=-1)
				{   HashSet<Country> territories=new HashSet<>();
					territories.addAll(continent.getTerritoriesContained());
					//territories.removeAll(almostconqueredP.get(Index).getTerritoriesOwned());
					territories=removeAll(almostconqueredP.get(Index),territories);
					//territories.removeAll(cplayer.getTerritoriesOwned());
					territories=removeAll(cplayer,territories);
					/*for(Country territory:territories)
						if(territory.getArmies()<6+game.getCountries().length/50)
							territories.remove(territory);*/
					if(territories.isEmpty())
						Tofortify1.add(ourcountries.get(0));
					else
						continue;
				}
				else
					continue;
			}
			Country defender=Tofortify1.get(Tofortify1.size()-1);
			HashSet<Country> neighbours=new HashSet<>();
			neighbours.addAll(defender.getIncomingNeighbours());
			neighbours=retainAll(continent,neighbours);
			//neighbours.retainAll(continent.getIncomingBorderCountries());
			betterdefence1=new HashSet<>();
			betterdefence1.addAll(betterdefence);
			worsedefence1=new HashSet<>();
			worsedefence1.addAll(worsedefence);
			betterdefence.addAll(neighbours);
			worsedefence.addAll(neighbours);
			threat=FindThreats(cplayer,defender,defender);
			betterdefence=new HashSet<>();
			betterdefence.addAll(betterdefence1);
			worsedefence=new HashSet<>();
			worsedefence.addAll(worsedefence1);
			threat=Math.max(threat,6);
			threat=(int)(threat*2/3-defender.getArmies());
			if(threat<=0)
			{   Tofortify1.remove(Tofortify1.size()-1);
				continue;
			}
			sum=(int)threat+2+game.getCountries().length/100;
			if(sum>extraarmies)
				sum=extraarmies;
			Tofortify2.add(sum);
			extraarmies-=sum;
			reinforcementprevented+=continents[index[i]].getArmyValue();
			if(extraarmies==0)
				break;
		}
		//osvajanje nedovoljnih branilaca u cilju bolje odbrane:
		for(i=0;i<continents.length;i++)
		{   sum=0;
			for(j=0;j<players.size();j++)
				sum+=matrix[i][j];
			if(sum==0)
				continue;
			Continent continent=allcontinents[index[i]];
			if(toremove.contains(continent))
				continue;
			if(continent.getTerritoriesContained().size()==1)
				continue;
			if(almostconquered.indexOf(continent)<0)
				continue;
			Player conqueror=almostconqueredP.get(almostconquered.indexOf(continent));
			if(conqueror==cplayer)
				continue;
			if(removeAll(conqueror,continent.getTerritoriesContained()).size()!=1)
				continue;
			Country defend=(Country)(removeAll(conqueror,continent.getTerritoriesContained()).get(0));
			Player defender=defend.getOwner();
			if(defender==cplayer)
				continue;
			//ako je branilac vec igrao, pa nije branio kontinent, ili ako nije, ali je preslab:
			List<Player> Players=new ArrayList<>();
			Players.addAll(players);
			for(j=0;j<Players.size();j++)
			{   Player playerr=Players.get(j);
				if(playerr!=conqueror&&playerr!=defender)
				{   Players.remove(0);
					j--;
				}
				else
					break;
			}
			if(Players.get(0)==defender)
			{   max=e;sum=0;Sum=0;min=e;
				for(Player playerr:players)
					if(playerr!=cplayer)
					{   int n=getReinforcements(playerr);
						Sum+=n;
						if(n>max)
							max=n;
						if(n>=e*4/3&&n>=e+2)
							sum++;
						if(n<min)
							min=n;
					}
				if(max>=2*e&&e<=(int)min*4/3&&sum*2>=game.getPlayers().size())
					indweak=1;
				else
					continue;
			}
			List<Country> countries=continent.getIncomingBorderCountries();
			countries=removeAll(cplayer,countries);
			countries=removeAll(conqueror,countries);
			countries=TerritoriesOnDistance(countries,-1,"max");
			countries=removeAll(continent,countries);
			countries=retainAll(cplayer,countries);
			for(Country country:countries)
			{   HashSet<Country> neighbours=new HashSet<>();
				neighbours.addAll(country.getNeighbours());
				neighbours=retainAll(continent,neighbours);
				neighbours=removeAll(conqueror,neighbours);
				int attack=country.getArmies();
				double threat;
				if(betterdefence.contains(country))
					threat=Math.max(threats[country.getColor()],3);
				else
					threat=3;
				attack-=threat;
				max=(int)Double.NEGATIVE_INFINITY;
				Country Indmax=null;
				for(Country neighbour:neighbours)
				{   int defence=neighbour.getArmies();
					int battle=(int)(attack-1.8*(Math.max(defence,1)-1));
					if(battle>max)
					{   max=battle;
						Indmax=neighbour;
					}
				}
				if(max<0&&max+extraarmies>0)
					attack+=extraarmies+max+Math.min(-max,2);
				if(Indmax!=null)
				{   Toattack.add(country);
					Todefend.add(Indmax);
					Attacktype.add(-1);
					Towinmove.add(3);
					Towinstay.add((int)Math.round(threat));
				}

			}
		}
		return reinforcementprevented*3;
	}

	private int BreakContinents(int extraarmies,
			 List<Country> Toattack, List<Country> Todefend, List<Integer> Attacktype, List<Integer> Towinmove, List<Integer> Towinstay, List<Country> Tofortify1, List<Integer> Tofortify2)
	{   int i,j,max,sum,min,indmax=0,reinforcementreduced=0;
		List<Player> players=game.getPlayers();
		int[] index=new int[game.getContinents().length];
		for(i=0;i<game.getContinents().length;i++)
			index[i]=i;
		double[] reinforcements=new double[game.getPlayers().size()];
		double[] values=new double[game.getContinents().length];
		Country[] indMax=new Country[game.getContinents().length];
		for(i=0;i<game.getPlayers().size();i++)
			reinforcements[i]=getReinforcements((Player)game.getPlayers().get(i));
		//Da li je igrac slab?
		int e=(int)reinforcements[game.getPlayers().indexOf(cplayer)];
		max=e;sum=0;min=e;
		for(Player player:players)
			if(player!=cplayer)
			{   int n=getReinforcements(player);
				if(n>max)
					max=n;
				if(n>=e*4/3&&n>=e+2)
					sum++;
				if(n<min)
					min=n;
			}
		if(max>=2*e&&e<=(int)min*4/3&&sum*2>=game.getPlayers().size())
			return 0;
		HashSet<Continent> toremove=new HashSet<>();
		for(Continent continent:game.getContinents())
			for(Player ally:game.alliance)
				if(continent.isOwned(ally))
					toremove.add(continent);
		if(toremove.size()==game.getContinents().length)
			return 0;
		Continent[] continents=new Continent[game.getContinents().length-toremove.size()];
		j=0;
		for(i=0;i<game.getContinents().length;i++)
			if(!toremove.contains(game.getContinents()[i]))
			{   continents[j]=game.getContinents()[i];
				j++;
			}
		Country[] paths=new Country[game.getCountries().length+1];
		double[] armies=new double[game.getCountries().length+1];
		double[] parameter=new double[continents.length];
		double[] armiesneed=new double[continents.length+1];
		List<Country> countries=new ArrayList<>();
		double threat;
		//trazenje najboljeg puta do skoro svakog kontinenta:
		countries.addAll(cplayer.getTerritoriesOwned());
		for(Country country:countries)
		{   threat=threats[country.getColor()];
			if(worsedefence.contains(country))
			{   if(extendedworsedefence.contains(country))
					threat=0;
				else
					threat=threat*2/3;
			}
			else if(almostconquered.contains(country.getContinent()))
				threat=threat*2/3;
			else if(!betterdefence.contains(country))
				threat=0;
			if(country.getArmies()+extraarmies-threat>3)
				armies[country.getColor()]=country.getArmies()+extraarmies-threat;
		}
		while(!countries.isEmpty())
		{   Country country=countries.get(0);
			HashSet<Country> neighbours=new HashSet<>();
			neighbours.addAll(country.getNeighbours());
			neighbours=removeAll(cplayer,neighbours);
			double attack=armies[country.getColor()]-1;
			//if(country==game.getCountries()[171-1])
			//    attack=attack;
			if(attack>3)
			for(Country neighbour:neighbours)
			{   double defence=neighbour.getArmies();
				double battle=1.8*(Math.max(defence,1)-1);
				/*if(neighbour==game.getCountries()[172-1])
					battle=battle;
				if(neighbour==game.getCountries()[170-1])
					battle=battle;*/
				if(attack-battle>armies[neighbour.getColor()])
				{   armies[neighbour.getColor()]=attack-battle;
					countries.add(neighbour);
					paths[neighbour.getColor()]=country;
				}
			}
			countries.remove(country);
		}
		//normiranje pojacanja:
		double Max,Min;
		Max=Min=reinforcements[0];
		for(i=1;i<game.getPlayers().size();i++)
		{   if(reinforcements[i]>Max)
				Max=reinforcements[i];
			if(reinforcements[i]<Min)
				Min=reinforcements[i];
		}
		for(i=0;i<game.getPlayers().size();i++)
		{   reinforcements[i]-=Min;
			reinforcements[i]=reinforcements[i]/(Max-Min)/2;
			reinforcements[i]+=0.5;
		}
		//normiranje vrednosti kontinenata:
		values[0]=continents[0].getArmyValue();
		Max=Min=values[0];
		for(i=0;i<continents.length;i++)
		{   Continent continent=continents[i];
			values[i]=continent.getArmyValue();
			if(values[i]>Max)
				Max=values[i];
			if(values[i]<Min)
				Min=values[i];
		}
		for(i=0;i<continents.length;i++)
		{   Continent continent=continents[i];
			values[i]=continent.getArmyValue();
			values[i]-=Min;
			values[i]=values[i]/(Max-Min)/2;
			values[i]+=0.5;
		}
		//racunanje parametra:
		for(i=0;i<continents.length;i++)
		{   Continent continent=continents[i];
			if(game.alliance.contains(cplayer))
			armiesneed[i]=Double.POSITIVE_INFINITY;
			parameter[i]=Double.POSITIVE_INFINITY;
			Player owner=continent.getOwner();
			if(owner==null||owner==cplayer)
				continue;
			countries=new ArrayList<>();
			countries.addAll(continent.getIncomingBorderCountries());
			Max=-extraarmies;
			for(Country country:countries)
				if(armies[country.getColor()]>0)
				{   threat=threats[country.getColor()];
					if(worsedefence.contains(country))
					{   if(extendedworsedefence.contains(country))
							threat=0;
						else
							threat=threat*2/3;
					}
					else if(almostconquered.contains(country.getContinent()))
						threat=threat*2/3;
					else if(!betterdefence.contains(country))
						threat=0;
					if(armies[country.getColor()]-threat-3>Max)
					{   Max=armies[country.getColor()]-threat-3;
						indMax[i]=country;
					}
				}
			if(indMax[i]==null)
				continue;
			if(Max>=0)
				armiesneed[i]=0;
			else if(Max<0&&Max+extraarmies>0)
				armiesneed[i]=-Max;
			else
				continue;
			parameter[i]=armiesneed[i]/values[i]/reinforcements[game.getPlayers().indexOf(owner)];
		}
		//sortiranje kontinenata po parametru:
		int P;
		for(i=0;i<continents.length-1;i++)
		{   Min=Double.POSITIVE_INFINITY;
			for(j=i+1;j<continents.length;j++)
				if(parameter[index[j]]<Min)
				{   Min=parameter[index[j]];
					indmax=j;
				}
			if(parameter[index[i]]>Min)
			{   P=index[indmax];
				index[indmax]=index[i];
				index[i]=P;
			}
		}
		Tofortify1.clear();
		Tofortify2.clear();
		//planiranje skidanja kontinenta:
		prvapetlja:
		for(i=0;i<continents.length;i++)
		{   if(armiesneed[index[i]]>extraarmies)
				break;
			Country country=indMax[index[i]];
			if(country==null)
				continue;
			double threat1=FindThreats(cplayer,country,country);
			if(continents[index[i]].getTerritoriesContained().size()>1)
				threat1=threat1*2/3-3;
			if(threat1<0)
				threat1=0;
			armiesneed[index[i]]+=threat1+2;
			if(armiesneed[index[i]]>extraarmies)
				armiesneed[index[i]]=extraarmies;
			Country defender=indMax[index[i]];
			Country attacker=paths[defender.getColor()];
			threat=threats[attacker.getColor()];
			if(worsedefence.contains(attacker))
			{   if(extendedworsedefence.contains(attacker))
					threat=0;
				else
					threat=threat*2/3;
			}
			else if(almostconquered.contains(attacker.getContinent()))
				threat=threat*2/3;
			else if(!betterdefence.contains(attacker))
				threat=0;
			threat=Math.max(threat,3);
			Toattack.add(attacker);
			Todefend.add(defender);
			Attacktype.add(-1);
			Towinmove.add(0);
			Towinstay.add((int)Math.round(threat));
			while(true)
			{   defender=attacker;
				attacker=paths[defender.getColor()];
				if(attacker==null)
					break;
				Toattack.add(0,attacker);
				Todefend.add(0,defender);
				Attacktype.add(0,-1);
				Towinmove.add(0,6);
				Towinstay.add(0,3);
			}
			Tofortify1.add(defender);
			Tofortify2.add((int)Math.round(armiesneed[index[i]]));
			if(continents[index[i]].getTerritoriesContained().size()==1)
				reinforcementreduced+=2*continents[index[i]].getArmyValue();
			else
				reinforcementreduced+=continents[index[i]].getArmyValue();
			extraarmies-=(int)Math.round(armiesneed[index[i]]);
		}
		return reinforcementreduced*3;
	}

	/**
	* Algoritmom pomeranja granica osvajamo oblast @param area, ili njen deo, ako je u pitanju cela tabla.
	* U oblasti su opkoljene teritorije @param surrounded.
	* Za osvajanje oblasti je potrebno @param extraarmies tenkova pojacanja.
	*/
	private int[] MovingBorders(List<Country> area, int extraarmies,
			 List<Country> Toattack, List<Country> Todefend, List<Integer> Attacktype, List<Integer> Towinmove, List<Integer> Towinstay, List<Country> Tofortify1, List<Integer> Tofortify2)
	{   //kopiramo trenutne vlasnike i broj tenkova teritorija da bismo gledali unapred, a posle cemo da vratimo:
		int Extraarmies=extraarmies;
		int[] povratnavrednost=new int[2];
		List<Player> owners=new ArrayList<>();
		List<Player> players=new ArrayList<>();
		players.addAll(game.getPlayers());
		int armies[]=new int[game.getCountries().length];
		for(int i=0;i<game.getCountries().length;i++)
		{   owners.add(game.getCountries()[i].getOwner());
			armies[i]=game.getCountries()[i].getArmies();
		}
		int i,index,j,ind;
		double max,min;
		List<Country> countries;
		HashSet<Country> neighbours;
		HashSet<Country> oneenemyneighbours=new HashSet<>();
		List<Country> moreenemyneighbours=new ArrayList<>();
		List<List<Country>> neighbourspercountry=new ArrayList<>();
		List<List<Double>> parameters=new ArrayList<>();
		List<List<Double>> reinforcementsneed=new ArrayList<>();
		List<List<Double>> attackthreats=new ArrayList<>();
		List<List<Double>> defendthreats=new ArrayList<>();
		/*countries.addAll(cplayer.getTerritoriesOwned());
		countries.removeAll(FindFullDefended(cplayer));
		for(Country country:countries)
		{   country.removeArmies(country.getArmies());
			country.addArmies(armies[country.getColor()-1]);
		}*/
		countries=new ArrayList<>();
		countries.addAll(cplayer.getTerritoriesOwned());
		if(extraarmies>0)
			countries.removeAll(game.forbiddenAttackers);
		//ovde nam trebaju unutrasnje teritorije koje ne mogu da napadaju:
		List<Country> Fulldefended=new ArrayList<>();
		Fulldefended.addAll(countries);
		for(i=0;i<Fulldefended.size();i++)
		{   Country country=Fulldefended.get(i);
			neighbours=new HashSet<>();
			neighbours.addAll(country.getNeighbours());
			neighbours.addAll(country.getIncomingNeighbours());
			if(!neighbours.isEmpty())
			{   Fulldefended.remove(i);
				i--;
			}
		}
		HashSet<Country> alliedcountries=new HashSet<>();
		if(game.alliance.contains(cplayer))
		for(Player ally:game.alliance)
			if(ally!=cplayer)
			{   alliedcountries.addAll(retainAll(ally,betterdefence));
				alliedcountries.addAll(retainAll(ally,worsedefence));
				alliedcountries.addAll(retainAll(ally,fulldefended));
			}
		neighbours=new HashSet<>();
		neighbours.addAll(TerritoriesOnDistance(countries,1,"max"));
		neighbours.removeAll(alliedcountries);
		countries.removeAll(Fulldefended);
		neighbours.removeAll(Fulldefended);
		//rasporedjujemo sve neighbours u neighbourspercountry:
		for(Country country:countries)
			neighbourspercountry.add(new ArrayList<>());
		for(Country neighbour:neighbours)
		{   HashSet<Country> neighbours1=new HashSet<>();
			if(neighbour.getOwner()==cplayer)
				continue;
			neighbours1.addAll(neighbour.getIncomingNeighbours());
			//neighbours1.retainAll(cplayer.getTerritoriesOwned());
			neighbours1=retainAll(cplayer,neighbours1);
			for(Country neighbour1:neighbours1)
			{   if(countries.contains(neighbour1))
				{   index=countries.indexOf(neighbour1);
					neighbourspercountry.get(index).add(neighbour);
				}
			}
		}
		//razbijamo countries na oneenemyneighbours i moreenemyneighbours; u drugu idu i sve teritorije u koju su moguci jednosmerni napadi:
		for(i=0;i<countries.size();i++)
		{   Country country=countries.get(i);
			HashSet<Country> neighbours1=new HashSet<>();
			HashSet<Country> lista=new HashSet<>();
			neighbours1.addAll(country.getIncomingNeighbours());
			neighbours1.removeAll(country.getNeighbours());
			//neighbours1.removeAll(cplayer.getTerritoriesOwned());
			neighbours1=removeAll(cplayer,neighbours1);
			lista.addAll(neighbourspercountry.get(i));
			lista.addAll(neighbours1);
			if(lista.size()==1&&neighbours1.isEmpty())
				oneenemyneighbours.add(country);
			else
				moreenemyneighbours.add(country);
		}
		// <editor-fold defaultstate="collapsed">
		//Za skoro sve teritorije iz oneenemyneighbours izbacujemo sve clanove od neighbourspercountry iz moreenemyneighbours.
		//Ako se tako broj neprijateljskih suseda, tj. mogucih napada smanji na 1,
		//teritorija se dodaje u oneenemyneighbours i prekida se dalje izbacivanje.
		/*List<Country> oneenemyneighbours1=new ArrayList<>();
		oneenemyneighbours1.addAll(oneenemyneighbours);
		oneenemyneighbours1.add(0,null);
		while(true)
		{   oneenemyneighbours1.remove(0);
			if(oneenemyneighbours1.isEmpty())
				break;
			Country oneenemyneighbour=oneenemyneighbours1.get(0);
			if(!countries.contains(oneenemyneighbour))
				continue;
			index=countries.indexOf(oneenemyneighbour);
			if(neighbourspercountry.get(index).isEmpty())
				continue;
			Country uniqueenemyneighbour=neighbourspercountry.get(index).get(0);
			for(i=0;i<moreenemyneighbours.size();i++)
			{   Country moreenemyneighbour=moreenemyneighbours.get(i);
				if(!moreenemyneighbour.isNeighbours(uniqueenemyneighbour))
					continue;
				index1=countries.indexOf(moreenemyneighbour);
				List<Country> lista=neighbourspercountry.get(index1);
				if(lista.contains(uniqueenemyneighbour))
				{   if(lista.size()>1)
						lista.remove(uniqueenemyneighbour);
					if(lista.size()==1)
					{   moreenemyneighbours.remove(moreenemyneighbour);
						i--;
						oneenemyneighbours.add(moreenemyneighbour);
						oneenemyneighbours1.add(moreenemyneighbour);
						ind=1;
					}
				}
			}
		}*/
		// </editor-fold>
		//Napad se moze izvrsiti ako je branilac u oblasti area ili ako je napad vise na jedan:
		List<Country> onenemyattackers=new ArrayList<>();
		for(i=0;i<neighbourspercountry.size();i++)
			if(neighbourspercountry.get(i).size()==1)
				onenemyattackers.add(countries.get(i));
		for(i=0;i<neighbourspercountry.size();i++)
		{   Country attacker=countries.get(i);
			neighbours=new HashSet<>();
			neighbours.addAll(attacker.getNeighbours());
			neighbours.retainAll(area);
			//neighbours.removeAll(cplayer.getTerritoriesOwned());
			neighbours=removeAll(cplayer,neighbours);
			int br1=onenemyattackers.indexOf(attacker);
			int br2=onenemyattackers.lastIndexOf(attacker);
			if(br1==br2&&neighbours.isEmpty())
			{   countries.remove(i);
				neighbourspercountry.remove(i);
				i--;
			}
		}
		int e=getReinforcements(cplayer);
		int Max=e,sum=0,Min=e,indweak=0;
		for(Player player:players)
			if(player!=cplayer)
			{   int n=getReinforcements(player);
				if(n>Max)
					Max=n;
				if(n>=e*4/3&&n>=e+2)
					sum++;
				if(n<Min)
					Min=n;
			}
		if(Max>=2*e&&e<=(int)Min*4/3&&sum*2>=game.getPlayers().size())
			indweak=1;
		//Racunamo parametar. Za teritorije u moreenemyneighbours ima mogucih parametara koliko i neprijateljskih suseda i sortiramo ih,
		//pa ce minimum biti na prvom mestu. Ako je neka teritorija u worsedefence, parametar je negativan.
		for(i=0;i<neighbourspercountry.size();i++)
		{   List<Country> lista=neighbourspercountry.get(i);
			List<Double> listofparameters=new ArrayList<>();
			parameters.add(listofparameters);
			List<Double> listofreinforcements=new ArrayList<>();
			reinforcementsneed.add(listofreinforcements);
			List<Double> listofatackthreats=new ArrayList<>();
			attackthreats.add(listofatackthreats);
			List<Double> listofdefendthreats=new ArrayList<>();
			defendthreats.add(listofdefendthreats);
			Country attacker=countries.get(i);
			//izvlacenje ispred zagrade zbog ubrzanja:
			for(Country defender:lista)
			{   if(!attacker.isNeighbours(defender))
					continue;
				if(!area.contains(defender))
				{   listofreinforcements.add(Double.POSITIVE_INFINITY);
					listofatackthreats.add(Double.POSITIVE_INFINITY);
					listofdefendthreats.add(Double.POSITIVE_INFINITY);
					listofparameters.add(Double.POSITIVE_INFINITY);
					continue;
				}
				//sve promenljive i parametar kao njihova funkcija:
				double centralization=game.sumofdistances[defender.getColor()-1];
				double threat;
				threat=FindThreats(cplayer,defender,defender);
				//try{threat=threats2.get(defender.getColor()).get(0);}
				//catch(Exception E){
				//    threat=FindThreats(cplayer,defender,defender);
				//}
				double threat1;
				if(!betterdefence.contains(attacker))
					threat=threat*2/3;
				//da li moze da se napad podrzi iz drugih teritorija:
				HashSet<Country> neighbours1=new HashSet<>();
				neighbours1.addAll(defender.getIncomingNeighbours());
				//neighbours1.retainAll(cplayer.getTerritoriesOwned());
				neighbours1=retainAll(cplayer,neighbours1);
				neighbours1.remove(attacker);
				double attack=attacker.getArmies();
				for(Country neighbour:neighbours1)
				{   if(!countries.contains(neighbour))
						continue;
					index=countries.indexOf(neighbour);
					if(neighbourspercountry.get(index).contains(defender))
					{   threat1=FindThreats(cplayer,neighbour,defender);
						index=neighbour.getNeighbours().indexOf(defender)+1;
						//try{threat1=threats2.get(neighbour.getColor()).get(index);}
						//catch(Exception E){
						//    threat1=FindThreats(cplayer,neighbour,defender);
						//}
						if(!betterdefence.contains(neighbour))
							threat1=threat1*2/3;
						attack+=Math.max(neighbour.getArmies()-(int)Math.max(3,threat1),0);
					}
				}
				Continent continent=attacker.getContinent();
				threat1=FindThreats(cplayer,attacker,defender);
				index=attacker.getNeighbours().indexOf(defender)+1;
				//try{threat1=threats2.get(attacker.getColor()).get(index);}
				//catch(Exception E){
				//    threat1=FindThreats(cplayer,attacker,defender);
				//}
				//ako okolo niko nista ne radi, moguce je igrati brze:
				if(!betterdefence.contains(attacker)&&(!almostconquered.contains(attacker.getContinent())))
				{   neighbours1=new HashSet<>();
					neighbours1.addAll(attacker.getIncomingNeighbours());
					neighbours1.remove(defender);
					//neighbours1.removeAll(cplayer.getTerritoriesOwned());
					neighbours1=removeAll(cplayer,neighbours1);
					ind=0;
					for(Country neighbour:neighbours1)
						if(neighbour.getArmies()>4)
						{   ind=1;
							break;
						}
					if(ind==0)
						threat1=threat1/2;
					if(!area.contains(attacker))
						threat1=Math.min(3,threat1);
					if(oneenemyneighbours.contains(attacker))
						threat=1.5*Math.max(game.getCountries().length/(3*game.getPlayers().size())/2,Math.max(3,threat1));
					else
						threat1=1.5*Math.max(game.getCountries().length/(3*game.getPlayers().size())/2,Math.max(3,threat1));
				}
				ind=0;
				neighbours1=new HashSet<>();
				neighbours1.addAll(defender.getIncomingNeighbours());
				//neighbours1.removeAll(cplayer.getTerritoriesOwned());
				neighbours1=removeAll(cplayer,neighbours1);
				for(Country neighbour:neighbours1)
					if(neighbour.getArmies()>4)
					{   ind=1;
						break;
					}
				if(ind==0)
					threat=threat/2;
				if(lista.size()==1||fulldefended.contains(attacker))
				{   if(!betterdefence.contains(attacker))
						threat1=threat1*2/3;
					threat1=Math.max(1,threat1);
				}
				else
				{   if(betterdefence.contains(attacker))
						threat1=Math.max(threat1,6);
					else
						threat1=threat1*2/3;
					threat1=Math.max(threat1,3);
				}
				if((!worsedefence.contains(attacker)||(extendedworsedefence.contains(attacker)&&defender.getArmies()<6))&&!betterdefence.contains(attacker)&&!almostconquered.contains(continent)/*&&smallmap==0*/)
				{   //threat1=Math.min(threat1,10);
					threat=Math.max(threat,1);
					threat=Math.min(threat,Math.max(10,defender.getArmies()));
				}
				//if(!worsedefence.contains(defender)&&!betterdefence.contains(defender)/*&&smallmap==0*/)
				/*{   //threat-=2;//korektivni broj
					threat=Math.max(threat,1);
					threat=Math.min(threat,10);
				}*/
				if(almostconquered.contains(continent))
					if(continent==defender.getContinent())
					{   if(almostconqueredP.get(almostconquered.indexOf(continent))!=defender.getOwner())
						if(almostconqueredP.get(almostconquered.indexOf(continent))!=attacker.getOwner())
						{   threat=Math.max(threat*2,6);
							threat1=threat1*2;
						}
					}
					else
						threat1+=2;
				double defence=defender.getArmies();
				double coeficient=(1+0.8*Math.min(1,(double)game.getCountries().length/game.getPlayers().size()/defence));
				coeficient=1.8;
				double armiesneed=(defence-1)*coeficient+1+threat+threat1-attack+2;
				//kol'ko teritorija fali do osvajanja kontinenta:
				double conqering=2-1/Math.sqrt(removeAll(cplayer,defender.getContinent().getTerritoriesContained()).size());
				neighbours1=new HashSet<>();
				neighbours1.addAll(defender.getNeighbours());
				neighbours1.addAll(defender.getIncomingNeighbours());
				neighbours1.removeAll(cplayer.getTerritoriesOwned());
				double enemyneighbours=Math.min(lista.size(),neighbours1.size()+1+(double)lista.size()/10);
				enemyneighbours=(2*enemyneighbours-1)/enemyneighbours;
				//Ako je branilac covek, pojacava se parametar da se oteza igra:
				double difficulty=1;
				if(defender.getOwner().getType() == Player.PLAYER_HUMAN)
					difficulty=1.5;
				double mission;//DODATI PARAMETAR ZA PRESTONICU ILI ZADATAK KAD BUDE RADJENO
				double parameter=armiesneed/centralization*conqering*enemyneighbours/difficulty;
				//parametri izmedju 0 i 2 se sabijaju na [1,2], a parametri < 0  na [0,1]:
				if(parameter<2&&parameter>=0)
					parameter=parameter/2+1;
				else if(parameter<0)
				{   
					parameter=armiesneed*centralization*conqering/enemyneighbours/difficulty;
					parameter=parameter-1;
					parameter=1/parameter;
					parameter=-parameter;
				}
				if(armiesneed<=0)
					armiesneed=0;
				listofreinforcements.add(armiesneed);
				listofatackthreats.add(threat1);
				listofdefendthreats.add(threat);
				if(!betterdefence.contains(attacker))
					parameter=-parameter;
				listofparameters.add(parameter);
			}
			//sortiranje liste po parametru:
			for(int I=0;I<listofparameters.size()-1;I++)
			{   min=Double.POSITIVE_INFINITY;
				index=I;
				double p;
				Country P;
				for(j=I+1;j<listofparameters.size();j++)
					if(Math.abs(listofparameters.get(j))<min)
					{   min=Math.abs(listofparameters.get(j));
						index=j;
					}
				if(min<Math.abs(listofparameters.get(I)))
				{   //parametri:
					p=listofparameters.get(I);
					listofparameters.set(I,listofparameters.get(index));
					listofparameters.set(index,p);
					//potrebna pojacanja:
					p=listofreinforcements.get(I);
					listofreinforcements.set(I,listofreinforcements.get(index));
					listofreinforcements.set(index,p);
					//teritorije:
					P=lista.get(I);
					lista.set(I,lista.get(index));
					lista.set(index,P);
					//pretnje napadima:
					p=listofatackthreats.get(I);
					listofatackthreats.set(I,listofatackthreats.get(index));
					listofatackthreats.set(index,p);
					//pretnje odbranama:
					p=listofdefendthreats.get(I);
					listofdefendthreats.set(I,listofdefendthreats.get(index));
					listofdefendthreats.set(index,p);
				}
			}
		}
		//trazimo najpovoljniji napad u slucaju da nista ne mozemo da napadnemo u ovom potezu:
		//sortiranje dinamicke matrice:
		for(i=0;i<parameters.size();i++)
		{   //System.out.printf("b %d\n",neighbourspercountry.get(i).size());
			if(parameters.get(i).isEmpty())
			{   parameters.remove(i);
				reinforcementsneed.remove(i);
				neighbourspercountry.remove(i);
				countries.remove(i);
				attackthreats.remove(i);
				defendthreats.remove(i);
				i--;
			}
		}
		/*System.out.printf("n %d %d\n",neighbourspercountry.size(),parameters.size());
		for(i=0;i<parameters.size();i++)
			System.out.printf("b %d\n",neighbourspercountry.get(i).size());*/
		for(i=0;i<neighbourspercountry.size()-1;i++)
		{   min=Double.POSITIVE_INFINITY;
			index=0;
			List<Double> p;
			List<Country> LP;
			Country P;
			for(j=i+1;j<neighbourspercountry.size();j++)
				if(Math.abs(parameters.get(j).get(0))<min)
				{   min=Math.abs(parameters.get(j).get(0));
					index=j;
				}
			if(Math.abs(parameters.get(i).get(0))>min)
			{   //parametri:
				p=parameters.get(i);
				parameters.set(i,parameters.get(index));
				parameters.set(index,p);
				//potrebna pojacanja:
				p=reinforcementsneed.get(i);
				reinforcementsneed.set(i,reinforcementsneed.get(index));
				reinforcementsneed.set(index,p);
				//neprijatelji:
				LP=neighbourspercountry.get(i);
				neighbourspercountry.set(i,neighbourspercountry.get(index));
				neighbourspercountry.set(index,LP);
				//teritorije:
				P=countries.get(i);
				countries.set(i,countries.get(index));
				countries.set(index,P);
				//pretnje napadima:
				p=attackthreats.get(i);
				attackthreats.set(i,attackthreats.get(index));
				attackthreats.set(index,p);
				//pretnje odbranama:
				p=defendthreats.get(i);
				defendthreats.set(i,defendthreats.get(index));
				defendthreats.set(index,p);
			}
		}
		if(reinforcementsneed.isEmpty())
			return new int[]{0,0};
		minattackers=new ArrayList<>();
		List<Integer> minreinforcementsneeds=new ArrayList<>();
		if(area.size()==game.getCountries().length)
			for(i=0;i<countries.size();i++)
			{   min=Double.POSITIVE_INFINITY;
				Country indmin=countries.get(i);
				for(j=0;j<countries.size();j++)
					if(reinforcementsneed.get(j).get(0)<min&&!minattackers.contains(countries.get(j)))
					{   min=reinforcementsneed.get(j).get(0);
						indmin=countries.get(j);
					}
				minattackers.add(indmin);
				minreinforcementsneeds.add((int)Math.round(min));
			}
		//Ubacujemo napade u plan.
		countries.size();
		glavnapetlja:
		while(!countries.isEmpty())
		{   List<Country> attackers=new ArrayList<>();
			attackers.add(countries.get(0));
			if(neighbourspercountry.get(0).isEmpty())
			{   countries.remove(0);
				reinforcementsneed.remove(0);
				neighbourspercountry.remove(0);
				parameters.remove(0);
				attackthreats.remove(0);
				defendthreats.remove(0);
				continue;
			}
			Country defender=neighbourspercountry.get(0).get(0);
			double threat=defendthreats.get(0).get(0);
			List<Double> attackersthreats=new ArrayList<>();
			attackersthreats.add(attackthreats.get(0).get(0));
			double attack;
			for(i=1;i<neighbourspercountry.size();i++)
			{   List<Country> lista=neighbourspercountry.get(i);
				if(lista.contains(defender)&&lista.size()==1)
					if(!attackers.contains(countries.get(i)))
					{   attackers.add(countries.get(i));
						index=neighbourspercountry.get(i).indexOf(defender);
						attackersthreats.add(attackthreats.get(i).get(index));
						countries.remove(i);
						reinforcementsneed.remove(i);
						neighbourspercountry.remove(i);
						parameters.remove(i);
						attackthreats.remove(i);
						defendthreats.remove(i);
					}
			}
			for(i=1;i<neighbourspercountry.size();i++)
			{   List<Country> lista=neighbourspercountry.get(i);
				if(lista.contains(defender)&&lista.size()>1)
					if(!attackers.contains(countries.get(i)))
					{   attackers.add(countries.get(i));
						index=neighbourspercountry.get(i).indexOf(defender);
						attackersthreats.add(attackthreats.get(i).get(index));
						reinforcementsneed.get(i).remove(index);
						neighbourspercountry.get(i).remove(index);
						parameters.get(i).remove(index);
						attackthreats.get(i).remove(index);
						defendthreats.get(i).remove(index);
					}
			}
			//glavni, tj. poslednji napad mora da se izvrsi od najjace strane:
			attack=attackers.get(0).getArmies()-(attackersthreats.get(0));
			max=(int)attack;
			for(i=1;i<attackers.size();i++)
			{   Country attacker=attackers.get(i);
				double attack1=attacker.getArmies()-attackersthreats.get(i);
				attack+=Math.max(attacker.getArmies()-attackersthreats.get(i),0);
				// <editor-fold defaultstate="collapsed">
				/*if((int)attack1>max)
				{   try{
					countries.add(0,countries.get(i));
					reinforcementsneed.add(0,reinforcementsneed.get(i));
					neighbourspercountry.add(0,neighbourspercountry.get(i));
					parameters.add(0,parameters.get(i));
					attackthreats.add(0,attackthreats.get(i));
					defendthreats.add(0,defendthreats.get(i));
					countries.remove(i+1);
					reinforcementsneed.remove(i+1);
					neighbourspercountry.remove(i+1);
					parameters.remove(i+1);
					attackthreats.remove(i+1);
					defendthreats.remove(i+1);}
					catch (Exception E)
					{
						max=max;
					}
				}*/
				// </editor-fold>
			}
			Country attacker=countries.get(0);
			double continentarmiesneed=0,armiesneed=reinforcementsneed.get(0).get(0);
			int wincontinent=0;
			//Da li je osvojen kontinent? Ako da, sve granice u okolini od 2+broj teritorija karte/50 dodati u betterdefence,
			//i pojacati ih, ako je moguce, a ako ne, teritorija se izbacuje iz liste i postaje kandidat za visepotezni plan:
			Player owner=defender.getOwner();
			owner.getTerritoriesOwned().remove(defender);
			defender.setOwner(cplayer);
			cplayer.getTerritoriesOwned().add(defender);
			List<Country> Tofortify11=new ArrayList<>();
			List<Integer> Tofortify21=new ArrayList<>();
			List<Country> Betterdefence=new ArrayList<>();
			if(defender.getContinent().isOwned(cplayer)&&defender.getContinent().getArmyValue()>0)
			{   //U sustini, kod je isti kao pri trazenju jace odbrane oko osvojenog kontinenta:
				Continent continent=defender.getContinent();
				HashSet<Country> bordercountries=new HashSet<>();
				HashSet<Country> bordercountries1=new HashSet<>();
				bordercountries.addAll(continent.getIncomingBorderCountries());
				for(Country country1:bordercountries)
					bordercountries1.addAll(country1.getIncomingNeighbours());
				//bordercountries1.removeAll(continent.getTerritoriesContained());
				bordercountries1=removeAll(continent,bordercountries1);
				bordercountries.addAll(bordercountries1);
				//bordercountries1.removeAll(cplayer.getTerritoriesOwned());
				bordercountries1=removeAll(cplayer,bordercountries1);
				//preventivna odbrana skoro svakog kontinenta:
				HashSet<Country> CrossContinentNeighbours;
				HashSet<Country> Oneenemyneighbours=new HashSet<>();
				prvapetlja:
				for(Country country:(List<Country>)continent.getTerritoriesContained())
				{   if(Betterdefence.contains(country)||betterdefence.contains(country))
						continue;
					CrossContinentNeighbours=new HashSet<>();
					CrossContinentNeighbours.addAll(country.getIncomingNeighbours());
					//CrossContinentNeighbours.removeAll(continent.getTerritoriesContained());
					CrossContinentNeighbours=removeAll(continent,CrossContinentNeighbours);
					if(CrossContinentNeighbours.isEmpty())
						continue;
					neighbours=new HashSet<>();
					neighbours.addAll(country.getIncomingNeighbours());
					//neighbours.removeAll(cplayer.getTerritoriesOwned());
					neighbours=removeAll(cplayer,neighbours);
					if(!neighbours.isEmpty())
					{   Betterdefence.add(country);
						continue;
					}
					for(Country country1:CrossContinentNeighbours)
						if((country1.getArmies()<6+game.getCountries().length/85&&!Betterdefence.contains(country1)&&!betterdefence.contains(country1)&&country1.getArmies()<=country.getArmies())||worsedefence.contains(country1))
						{   Betterdefence.remove(country);
							Betterdefence.add(country);
							if(CrossContinentNeighbours.size()==1)
								Oneenemyneighbours.add(country);
							continue prvapetlja;
						}
					Betterdefence.removeAll(CrossContinentNeighbours);
					Betterdefence.addAll(CrossContinentNeighbours);
				}
				int count=0;    
				while(true)
				{   ind=0;
					count++;
					//Izbacimo viskove koji nisu uoceni jer su ranije upisani:
					prvapetlja:
					for(i=0;i<Betterdefence.size();i++)
					{   Country country=Betterdefence.get(i);
						neighbours=new HashSet<>();
						neighbours.addAll(country.getIncomingNeighbours());
						//neighbours.removeAll(cplayer.getTerritoriesOwned());
						neighbours=removeAll(cplayer,neighbours);
						if(!neighbours.isEmpty())
							continue;
						CrossContinentNeighbours=new HashSet<>();
						CrossContinentNeighbours.addAll(country.getIncomingNeighbours());
						//CrossContinentNeighbours.removeAll(country.getContinent().getTerritoriesContained());
						CrossContinentNeighbours=removeAll(country.getContinent(),CrossContinentNeighbours);
						if(CrossContinentNeighbours.isEmpty())
							continue;
						for(Country country1:CrossContinentNeighbours)
							if(!Betterdefence.contains(country1)&&!betterdefence.contains(country1))
								continue prvapetlja;
						Betterdefence.remove(country);
						ind=1;
						i--;
					}
					//moze li se odbrana kontinenata pomeriti tako da bude manje teritorija:
					prvapetlja:
					for(Country country:bordercountries)
						if(!Betterdefence.contains(country)&&!betterdefence.contains(country))
						{   neighbours=new HashSet<>();
							neighbours.addAll(country.getIncomingNeighbours());
							neighbours.retainAll(Oneenemyneighbours);
							int ind1=0;
							for(Country country1:neighbours)
								if(worsedefence.contains(country1))
									continue prvapetlja;
								else if(country1.getArmies()>=country.getArmies())
									ind1=1;
							if(neighbours.size()>1&&ind1==1)
							{   Betterdefence.removeAll(neighbours);
								Betterdefence.add(country);
								ind=1;
							}
						}
					if(count>25)
						break;
					if(ind==0)
						break;
				}
				List<Country> Worsedefence=new ArrayList<>();
				Worsedefence.addAll(worsedefence);
				//Worsedefence.retainAll(cplayer.getTerritoriesOwned());
				Worsedefence=retainAll(cplayer,Worsedefence);
				List<Country> from=TerritoriesOnDistance(Worsedefence,-4-game.getCountries().length/50,"all");
				double[] Threats=FindThreats(from,Betterdefence,cplayer);
				for(Country country1:Betterdefence)
					if(countries.contains(country1))
					{   index=countries.indexOf(country1);
						double parameter=parameters.get(index).get(0);
						if(parameter<0)
						{   //prebacujemo u betterdefence tako sto parametru brisemo minus, tj. postaje pozitivan:
							parameters.get(index).set(0,Math.abs(parameter));
						}
					}
				wincontinent=1;
				// <editor-fold defaultstate="collapsed">
				/*sum=0;
				for(Country country1:Betterdefence)
				{   double threatt=Threats[country1.getColor()];
					if(country1.getArmies()<threatt)
					{   Tofortify11.add(country1);
						int n=(int)Math.round(threatt)-country1.getArmies();
						Tofortify21.add(n);
						sum+=n;
						continentarmiesneed+=n;
					}
				}
				continentarmiesneed-=extraarmies;
				if(sum>extraarmies)
				{   int tofortify[]=new int[Tofortify11.size()];
					while(extraarmies>0)
						for(i=0;i<Tofortify11.size();i++)
							if(tofortify[i]<Tofortify21.get(i))
							{   tofortify[i]++;
								extraarmies--;
								if(extraarmies==0)
									break;
							}
					for(i=0;i<Tofortify11.size();i++)
					{   Tofortify21.set(i,tofortify[i]);
						if(Tofortify21.get(i)==0)
						{   Tofortify11.remove(i);
							Tofortify21.remove(i);
						}
					}
				}
				if(minattacker==attacker&&!Tofortify11.isEmpty())
				{   minattackers.clear();
					minattackers.addAll(Tofortify11);
					minreinforcementsneeds.clear();
					minreinforcementsneeds.addAll(Tofortify21);
				}*/
				// </editor-fold>
			}
			defender.setOwner(owner);
			defender.getOwner().getTerritoriesOwned().add(defender);
			cplayer.getTerritoriesOwned().remove(defender);
			double attackparameter=Double.POSITIVE_INFINITY;
			Country Attacker=attacker;
			List<Double> Attackparameter=new ArrayList<>();
			List<Country> Attackneighbourspercountry=new ArrayList<>();
			if(!parameters.isEmpty()&&!parameters.get(0).isEmpty())
			{   attackparameter=parameters.get(0).get(0);
				Attacker=attacker;
				Attackparameter=parameters.get(0);
				Attackneighbourspercountry=neighbourspercountry.get(0);
			}
			//double parameter=Double.POSITIVE_INFINITY;
			//if(!parameters.isEmpty()&&!parameters.get(0).isEmpty())
			//    parameter=parameters.get(0).get(0);
			if(wincontinent==0||neighbourspercountry.get(0).size()==1)
			{   countries.remove(0);
				reinforcementsneed.remove(0);
				neighbourspercountry.remove(0);
				parameters.remove(0);
				attackthreats.remove(0);
				defendthreats.remove(0);
				if(Math.round(continentarmiesneed)>extraarmies||armiesneed>10000)
					continue;
				/*if((betterdefence.contains(defender)||worsedefence.contains(defender)||almostconquered.contains(defender.getContinent()))&&Math.round(armiesneed)>extraarmies)
					continue;*/
			}
			else
			{   if(Math.round(continentarmiesneed)>extraarmies||armiesneed>10000)
				{   if(!reinforcementsneed.get(0).isEmpty())
						reinforcementsneed.get(0).remove(0);
					if(!neighbourspercountry.get(0).isEmpty())
						neighbourspercountry.get(0).remove(0);
					if(!parameters.get(0).isEmpty())
						parameters.get(0).remove(0);
					if(!attackthreats.get(0).isEmpty())
						attackthreats.get(0).remove(0);
					if(!defendthreats.get(0).isEmpty())
						defendthreats.get(0).remove(0);
					continue;
				}
				// <editor-fold defaultstate="collapsed">
				/*if((betterdefence.contains(defender)||worsedefence.contains(defender)||almostconquered.contains(defender.getContinent()))&&Math.round(armiesneed)>extraarmies)
				{   reinforcementsneed.get(0).remove(0);
					neighbourspercountry.get(0).remove(0);
					parameters.get(0).remove(0);
					attackthreats.get(0).remove(0);
					defendthreats.get(0).remove(0);
					continue;
				}*/
				// </editor-fold>
				else
				{   countries.remove(0);
					reinforcementsneed.remove(0);
					neighbourspercountry.remove(0);
					parameters.remove(0);
					attackthreats.remove(0);
					defendthreats.remove(0);
				}
			}
			if(Math.round(continentarmiesneed)>extraarmies)
			{   
				Tofortify1.add(attackers.get(attackers.size()-1));
				Tofortify2.add(Extraarmies);
				extraarmies=0;
				continue;
			}
			Tofortify1.addAll(Tofortify11);
			Tofortify2.addAll(Tofortify21);
			for(i=0;i<Tofortify11.size();i++)
				if(attackers.contains(Tofortify11.get(i)))
					attack+=Tofortify21.get(i);
			if(attack+extraarmies<=defender.getArmies()-3+threat)
				continue;
			if(wincontinent==1)
			{   betterdefence.add(attacker);
				worsedefence.remove(attacker);
				betterdefence.addAll(Betterdefence);
			}
			//Za skoro svaki planiran napad izbacujemo napadaca iz oneenemyneighbours, ne i iz moreenemyneighbours
			//i ubacujemo osvojenu teritoriju na mesto koje odgovara izracunatom parametru.
			//double threat=threats2[defender.getColor()];
			//double threat1=0;
			//if(parameter<0)
			//   threat=threat*2/3;
			//ako je napad vise na jednog, trazimo najboljeg osvajaca, po mogucstvu koji napada 1 na 1,
			//tj. najveci ostatak od pretnji, i njega postavljamo da napadne na kraju.
			max=0;
			index=0;
			for(i=0;i<attackers.size();i++)
				if(attackers.get(i).getArmies()-attackersthreats.get(i)>max)
				{   max=attackers.get(i).getArmies()-attackersthreats.get(i);
					index=i;
				}
			attackers.add(attackers.get(index));
			attackersthreats.add(attackersthreats.get(index));
			attackers.remove(index);
			attackersthreats.remove(index);
			double threat1;
			attack=0;
			for(i=0;i<attackers.size();i++)
			{   attacker=attackers.get(i);
				attack+=Math.max(attacker.getArmies()-3,0);
				threat1=attackersthreats.get(i);
				if(attacker.getArmies()<(int)threat1+3&&i!=attackers.size()-1)
					continue;
				//threat1=FindThreats(cplayer,attacker,defender);
				//if(parameter<0)
				//    threat1=threat1*2/3;
				Toattack.add(attacker);
				Todefend.add(defender);
				if(i==attackers.size()-1)
				{   Attacktype.add(0);
					if((int)armiesneed<=(int)extraarmies)
						povratnavrednost[0]++;
					if((int)armiesneed>0&&extraarmies>0)
					{   extraarmies-=(int)Math.round(armiesneed);
						if(extraarmies>=3)
						{   armiesneed+=3;
							extraarmies-=3;
						}
						else if(extraarmies>0)
						{   armiesneed+=extraarmies;
							extraarmies=0;
						}
						Tofortify1.add(attacker);
						Tofortify2.add((int)Math.round(armiesneed));
					}
					if(oneenemyneighbours.contains(attacker))
					{   if((int)threat1==1)
							threat1=0;
						threat=Math.max(game.getCountries().length/(3*game.getPlayers().size())/2,Math.max(3,threat1));
						Towinmove.add((int)Math.round(Math.max(threat,3)));
						Towinstay.add((int)Math.round(Math.max(threat1,0)));
					}
					else if(fulldefended.contains(attacker))
					{   Towinmove.add((int)Math.round(Math.max(threat,3)));
						Towinstay.add((int)Math.round(Math.max(threat1,1)));
					}
					else
					{   Towinmove.add((int)Math.round(Math.max(threat,2)));
						Towinstay.add((int)Math.round(Math.max(threat1,2)));
					}
				}
				else
				{   Attacktype.add(3);
					Towinmove.add(0);
					if(oneenemyneighbours.contains(attacker))
						Towinstay.add((int)Math.round(Math.max(threat1,1)));
					else
						Towinstay.add((int)Math.round(Math.max(threat1,2)));
				}
				if(!area.contains(attacker))
				{   Attacktype.remove(Attacktype.size()-1);
					Attacktype.add(-1);
				}
			}
			if(Toattack.isEmpty())
				continue;
			//attacker=attackers.get(0);
			attack-=(int)Math.round((defender.getArmies()-1)*1.8+1);
			int move=0,stay=0;
			try
			{   move=Towinmove.get(Towinmove.size()-1);
				stay=Towinstay.get(Towinstay.size()-1);
			}
			catch (Exception ex)
			{
				//move=move; 
			}
			if(move==2&&stay==2||move==2&&stay==3)
			{   move=(int)attack/2;
				stay=(int)attack-move;
				if(stay<3)
				{   move-=3-stay;
					stay=3;
				}
			}
			else
			{   if(stay==2)
					stay=3;
				if(stay==0)
					stay=1;
				if(move==2)
					move=3;
				move=Math.max(move,3);
				move=(int)attack-stay;
			}
			if(move+stay>attack)
				move=(int)attack-stay;
			move=Math.max(move,3);
			attacker.removeArmies(attacker.getArmies());
			attacker.addArmies(stay);
			defender.removeArmies(defender.getArmies());
			defender.addArmies(move);
			defender.getOwner().getTerritoriesOwned().remove(defender);
			defender.setOwner(cplayer);
			cplayer.getTerritoriesOwned().add(defender);
			if(betterdefence.contains(attacker)||attacker.getContinent().isOwned(cplayer))
			{   HashSet<Country> neighbours1=new HashSet<>();
				neighbours1.addAll(attacker.getIncomingNeighbours());
				int Ind=0;
				for(Country neighbour:neighbours1)
					if(neighbour.getOwner()!=cplayer)
					{   Ind=1;
						break;
					}
				if(Ind==0)
				{   if(attacker.getArmies()==3)
					{   attacker.removeArmies(2);
						defender.addArmies((int)2);
					}
					worsedefence.removeAll(neighbours1);
					betterdefence.addAll(neighbours1);
					betterdefence.removeAll(FindFullDefended(cplayer));
					betterdefence.remove(attacker);
					worsedefence.remove(attacker);
					if(!betterdefence.contains(defender)&&!worsedefence.contains(defender))
						worsedefence.add(defender);
				}
			}
			else if(worsedefence.contains(attacker))
			{   HashSet<Country> neighbours1=new HashSet<>();
				neighbours1.addAll(attacker.getIncomingNeighbours());
				int Ind=0;
				for(Country neighbour:neighbours1)
					if(neighbour.getOwner()!=cplayer)
					{   Ind=1;
						break;
					}
				if(Ind==0)
				{   if(attacker.getArmies()==3)
					{   attacker.removeArmies(2);
						defender.addArmies((int)2);
					}
					worsedefence.addAll(neighbours1);
					worsedefence.removeAll(FindFullDefended(cplayer));
					worsedefence.removeAll(betterdefence);
					betterdefence.remove(attacker);
					worsedefence.remove(attacker);
					if(!betterdefence.contains(defender)&&!worsedefence.contains(defender))
						worsedefence.add(defender);
				}
			}
			//ako je osvojena cela predvidjena oblast, nastavljamo osvajanje karte:
			HashSet<Country> area1=new HashSet<>();
			area1.addAll(area);
			//area1.removeAll(cplayer.getTerritoriesOwned());
			area1=removeAll(cplayer,area1);
			if(area1.isEmpty())
			{   area=new ArrayList<>();
				area.addAll(Arrays.asList(game.getCountries()));
			}
			//dodajemo u odgovarajuce liste sve elemente defendera kao buduceg napadaca:
			countries.add(defender);
			//izbacujemo defendera sa svih mesta u neighbourspercountry, pa ubacujemo njegovu posebnu listu:
			for(i=0;i<parameters.size();i++)
			{   List<Country> lista=neighbourspercountry.get(i);
				if(!lista.contains(defender))
					continue;
				//index=lista.indexOf(defender);
				lista.remove(defender);
				//parameters.get(i).remove(index);
				//reinforcementsneed.get(i).remove(index);
			}
			List<Country> neighbours11=new ArrayList<>();
			neighbours11.addAll(defender.getNeighbours());
			//neighbours11.removeAll(cplayer.getTerritoriesOwned());
			neighbours11=removeAll(cplayer,neighbours11);
			neighbours11.removeAll(alliedcountries);
			neighbourspercountry.add(neighbours11);
			parameters.add(new ArrayList<>());
			reinforcementsneed.add(new ArrayList<>());
			attackthreats.add(new ArrayList<>());
			defendthreats.add(new ArrayList<>());
			//ubacujemo ga u oneenemyneighbours ili moreenemyneighbours; u drugu ide i ako su moguci jednosmerni napadi:
			index=countries.indexOf(defender);
			HashSet<Country> neighbours1=new HashSet<>();
			HashSet<Country> Lista=new HashSet<>();
			Lista.addAll(neighbourspercountry.get(index));
			neighbours1.addAll(defender.getIncomingNeighbours());
			neighbours1.removeAll(defender.getNeighbours());
			//neighbours1.removeAll(cplayer.getTerritoriesOwned());
			neighbours1=removeAll(cplayer,neighbours1);
			Lista.addAll(neighbours1);
			if(Lista.size()==1)
				oneenemyneighbours.add(defender);
			else
				moreenemyneighbours.add(defender);
			// <editor-fold defaultstate="collapsed">
			//Za skoro sve teritorije iz oneenemyneighbours izbacujemo sve clanove od neighbourspercountry iz moreenemyneighbours.
			//Ako se tako broj neprijateljskih suseda, tj. mogucih napada smanji na 1,
			//teritorija se dodaje u oneenemyneighbours i prekida se dalje izbacivanje.
			/*oneenemyneighbours1=new ArrayList<>();
			oneenemyneighbours1.addAll(oneenemyneighbours);
			oneenemyneighbours1.add(0,null);
			while(true)
			{   oneenemyneighbours1.remove(0);
				if(oneenemyneighbours1.isEmpty())
					break;
				Country oneenemyneighbour=oneenemyneighbours1.get(0);
				if(!countries.contains(oneenemyneighbour))
					continue;
				index=countries.indexOf(oneenemyneighbour);
				if(neighbourspercountry.get(index).isEmpty())
					continue;
				Country uniqueneighbour=neighbourspercountry.get(index).get(0);
				for(i=0;i<moreenemyneighbours.size();i++)
				{   Country moreenemyneighbour=moreenemyneighbours.get(i);
					if(!moreenemyneighbour.isNeighbours(uniqueneighbour))
						continue;
					if(!countries.contains(moreenemyneighbour))
						continue;
					index1=countries.indexOf(moreenemyneighbour);
					List<Country> lista=neighbourspercountry.get(index1);
					if(lista.contains(uniqueneighbour))
					{   if(lista.size()>1)
							lista.remove(uniqueneighbour);
						if(lista.size()==1)
						{   moreenemyneighbours.remove(moreenemyneighbour);
							oneenemyneighbours.add(moreenemyneighbour);
							oneenemyneighbours1.add(moreenemyneighbour);
						}
					}
				}
			}*/
			// </editor-fold>
			//Racunamo parametar. Za teritorije u moreenemyneighbours ima mogucih parametara koliko i neprijateljskih suseda i sortiramo ih,
			//pa ce minimum biti na prvom mestu. Ako je neka teritorija u worsedefence, parametar je negativan.
			for(i=0;i<neighbourspercountry.size();i++)
			{   List<Country> lista=neighbourspercountry.get(i);
				List<Double> listofparameters=parameters.get(i);
				List<Double> listofreinforcements=reinforcementsneed.get(i);
				List<Double> listofatackthreats=attackthreats.get(i);
				List<Double> listofdefendthreats=defendthreats.get(i);
				int n=listofparameters.size();
				attacker=countries.get(i);
				for(j=listofparameters.size();j<lista.size();j++)
				{   Country Defender=lista.get(j);
					if(!attacker.isNeighbours(Defender))
						continue;
					//sve promenljive i parametar kao njihova funkcija:
					double centralization=game.sumofdistances[Defender.getColor()-1];
					try{threat=threats2.get(Defender.getColor()).get(0);}
					catch(Exception E){
						threat=FindThreats(cplayer,Defender,Defender);
					}
					//threat=threats[Defender.getColor()];
					if(attackparameter<0)
						threat=threat*2/3;
					attack=attacker.getArmies();
					//da li moze da se napad podrzi iz drugih teritorija:
					neighbours1=new HashSet<>();
					neighbours1.addAll(Defender.getIncomingNeighbours());
					//neighbours1.retainAll(cplayer.getTerritoriesOwned());
					neighbours1=retainAll(cplayer,neighbours1);
					neighbours1.remove(attacker);
					for(Country neighbour:neighbours1)
					{   if(!countries.contains(neighbour))
							continue;
						index=countries.indexOf(neighbour);
						if(neighbourspercountry.get(index).contains(Defender))
						{   threat1=FindThreats(cplayer,neighbour,Defender);
							if(!betterdefence.contains(neighbour))
								threat1=threat1*2/3;
							attack+=Math.max(neighbour.getArmies()-(int)Math.max(3,threat1),0);
						}
					}
					threat1=FindThreats(cplayer,attacker,Defender);
					//ako okolo niko nista ne radi, moguce je igrati brze:
					if(!betterdefence.contains(attacker)&&(!almostconquered.contains(attacker.getContinent())))
					{   neighbours1=new HashSet<>();
						neighbours1.addAll(attacker.getIncomingNeighbours());
						neighbours1.remove(Defender);
						//neighbours1.removeAll(cplayer.getTerritoriesOwned());
						neighbours1=removeAll(cplayer,neighbours1);
						ind=0;
						for(Country neighbour:neighbours1)
							if(neighbour.getArmies()>4)
							{   ind=1;
								break;
							}
						if(ind==0)
							threat1=threat1/2;
						if(!area.contains(attacker))
							threat1=Math.min(3,threat1);
					if(oneenemyneighbours.contains(attacker))
						threat=1.5*Math.max(game.getCountries().length/(3*game.getPlayers().size())/2,Math.max(3,threat1));
					else
						threat1=1.5*Math.max(game.getCountries().length/(3*game.getPlayers().size())/2,Math.max(3,threat1));
					}
					ind=0;
					neighbours1=new HashSet<>();
					neighbours1.addAll(Defender.getIncomingNeighbours());
					//neighbours1.removeAll(cplayer.getTerritoriesOwned());
					neighbours1=removeAll(cplayer,neighbours1);
					for(Country neighbour:neighbours1)
						if(neighbour.getArmies()>4)
						{   ind=1;
							break;
						}
					if(ind==0)
						threat=threat/2;
					if(lista.size()==1||fulldefended.contains(attacker))
					{   if(!betterdefence.contains(attacker))
							threat1=threat1*2/3;
						threat1=Math.max(1,threat1);
					}
					else
					{   if(betterdefence.contains(attacker))
							threat1=Math.max(threat1,6);
						else
							threat1=threat1*2/3;
						threat1=Math.max(threat1,3);
					}
					Continent continent=attacker.getContinent();
					if((!worsedefence.contains(attacker)||(extendedworsedefence.contains(attacker)&&Defender.getArmies()<6))&&!betterdefence.contains(attacker)&&!almostconquered.contains(continent)/*&&smallmap==0*/)
					{   //threat1=Math.min(threat1,10);
						threat=Math.max(threat,1);
						threat=Math.min(threat,Math.max(10,defender.getArmies()));
					}
					//if(!worsedefence.contains(Defender)&&!betterdefence.contains(Defender)/*&&smallmap==0*/)
					/*{   //threat-=2;//korektivni broj
						threat=Math.max(threat,1);
						threat=Math.min(threat,10);
					}*/
					if(almostconquered.contains(continent))
						if(continent==defender.getContinent())
						{   if(almostconqueredP.get(almostconquered.indexOf(continent))!=defender.getOwner())
							if(almostconqueredP.get(almostconquered.indexOf(continent))!=attacker.getOwner())
							{   threat=threat*2;
								threat1=threat1*2;
							}
						}
						else
							threat1+=2;
					double defence=Defender.getArmies();
					//kol'ko teritorija fali do osvajanja kontinenta:
					double conqering=2-1/Math.sqrt(removeAll(defender.getContinent(),cplayer.getTerritoriesOwned()).size());
					double coeficient=(1+0.8*Math.min(1,(double)game.getCountries().length/game.getPlayers().size()/defence));
					coeficient=1.8;
					armiesneed=(defence-1)*coeficient+1+threat+threat1-attack;
					neighbours1=new HashSet<>();
					neighbours1.addAll(defender.getNeighbours());
					neighbours1.addAll(defender.getIncomingNeighbours());
					neighbours1.removeAll(cplayer.getTerritoriesOwned());
					double enemyneighbours=Math.min(lista.size(),neighbours1.size()+1+lista.size()/10);
					enemyneighbours=(2*enemyneighbours-1)/enemyneighbours;
					double difficulty=1;
					if(defender.getOwner().getType() == Player.PLAYER_HUMAN)
						difficulty=1.5;
					double mission;//DODATI PARAMETAR ZA PRESTONICU ILI ZADATAK KAD BUDE RADJENO
					double parameter=armiesneed/centralization*conqering*enemyneighbours/difficulty;
					//parametri izmedju 0 i 2 se sabijaju na [1,2], a parametri < 0  na [0,1]:
					if(parameter<2&&parameter>=0)
						parameter=parameter/2+1;
					else if(parameter<0)
					{   parameter=armiesneed*centralization/enemyneighbours/difficulty;
						parameter=parameter-1;
						parameter=1/parameter;
						parameter=-parameter;
					}
					listofatackthreats.add(threat1);
					listofdefendthreats.add(threat);
					if(armiesneed<=0)
						armiesneed=0;
					listofreinforcements.add(armiesneed);
					if(attackparameter<0)
						parameter=-parameter;
					listofparameters.add(parameter);
				}
				//sortiranje liste po parametru:
				if(listofparameters.size()>n)
					for(i=0;i<listofparameters.size()-1;i++)
					{   min=Double.POSITIVE_INFINITY;
						index=0;
						double p;
						Country P;
						for(j=i+1;j<listofparameters.size();j++)
							if(Math.abs(listofparameters.get(j))<min)
							{   min=Math.abs(listofparameters.get(j));
								index=j;
							}
						if(min<Math.abs(listofparameters.get(i)))
						{   //parametri:
							p=listofparameters.get(i);
							listofparameters.set(i,listofparameters.get(index));
							listofparameters.set(index,p);
							//potrebna pojacanja:
							p=listofreinforcements.get(i);
							listofreinforcements.set(i,listofreinforcements.get(index));
							listofreinforcements.set(index,p);
							//teritorije:
							P=lista.get(i);
							lista.set(i,lista.get(index));
							lista.set(index,P);
							//pretnje napadima:
							p=listofatackthreats.get(i);
							listofatackthreats.set(i,listofatackthreats.get(index));
							listofatackthreats.set(index,p);
							//pretnje odbranama:
							p=listofdefendthreats.get(i);
							listofdefendthreats.set(i,listofdefendthreats.get(index));
							listofdefendthreats.set(index,p);
						}
					}
				}
			// <editor-fold defaultstate="collapsed">
			//da li je bolje prebaciti ili ostaviti visak posle osvajanja zavisi ciji parametar je manji:
			/*for(j=0;j<Attackneighbourspercountry.size();j++)
			{   Country neighbour=Attackneighbourspercountry.get(j);
				if(Todefend.contains(neighbour))
				{   Attackneighbourspercountry.remove(j);
					Attackparameter.remove(j);
					j--;
				}
			}
			if(Attackneighbourspercountry.size()>0&&parameters.size()>0&&parameters.get(0).size()>0)
			{   List<Double> Parameter=parameters.get(parameters.size()-1);
				if(!Parameter.isEmpty())
				if(Parameter.size()<Attackparameter.size()||(Parameter.size()==Attackparameter.size()&&Math.abs(Parameter.get(0))<Math.abs(Attackparameter.get(0))))
				{   threat=threats2[Attacker.getColor()];
					//threat=threats[Attacker.getColor()];
					if(Attackparameter.get(0)<0)
						threat=threat*2/3;
					threat=Math.max(threat,3);
					if(betterdefence.contains(Attacker))
						threat=Math.max(threat,6);
					int armies1=Towinstay.get(Towinstay.size()-1);
					int armies2=Towinmove.get(Towinmove.size()-1);
					Towinstay.set(Towinstay.size()-1,(int)Math.round(threat));
					Towinmove.set(Towinmove.size()-1,armies1+armies2-(int)Math.round(threat));
				}
			}*/
			// </editor-fold>
			for(i=0;i<neighbourspercountry.size();i++)
			{   neighbourspercountry.get(i).remove(defender);
				attacker=countries.get(i);
				if(neighbourspercountry.get(i).isEmpty())
				{   neighbourspercountry.remove(i);
					countries.remove(attacker);
					oneenemyneighbours.remove(attacker);
					moreenemyneighbours.remove(attacker);
					parameters.remove(i);
					reinforcementsneed.remove(i);
					attackthreats.remove(i);
					defendthreats.remove(i);
				}
			}
			oneenemyneighbours.remove(Attacker);
			moreenemyneighbours.remove(Attacker);
			//sortiranje dinamicke matrice:
			for(i=0;i<parameters.size();i++)
				if(parameters.get(i).isEmpty())
				{   parameters.remove(i);
					reinforcementsneed.remove(i);
					neighbourspercountry.remove(i);
					countries.remove(i);
					attackthreats.remove(i);
					defendthreats.remove(i);
					i--;
				}
			for(i=0;i<parameters.size()-1;i++)
			{   min=Double.POSITIVE_INFINITY;
				if(parameters.get(i).isEmpty())
					System.out.printf("%d. niz parametara je prazan.\n",i);
				index=0;
				List<Double> p;
				List<Country> LP;
				Country P;
				for(j=i+1;j<parameters.size();j++)
					if(Math.abs(parameters.get(j).get(0))<min)
					{   min=Math.abs(parameters.get(j).get(0));
						index=j;
					}
				if(Math.abs(parameters.get(i).get(0))>min)
				{   //parametri:
					p=parameters.get(i);
					parameters.set(i,parameters.get(index));
					parameters.set(index,p);
					//potrebna pojacanja:
					p=reinforcementsneed.get(i);
					reinforcementsneed.set(i,reinforcementsneed.get(index));
					reinforcementsneed.set(index,p);
					//neprijatelji:
					LP=neighbourspercountry.get(i);
					neighbourspercountry.set(i,neighbourspercountry.get(index));
					neighbourspercountry.set(index,LP);
					//teritorije:
					P=countries.get(i);
					countries.set(i,countries.get(index));
					countries.set(index,P);
					//pretnje napadima:
					p=attackthreats.get(i);
					attackthreats.set(i,attackthreats.get(index));
					attackthreats.set(index,p);
					//pretnje odbranama:
					p=defendthreats.get(i);
					defendthreats.set(i,defendthreats.get(index));
					defendthreats.set(index,p);
				}
			}
		}
		if(extraarmies>0)
		{   if(!Toattack.isEmpty())
			{   //dodeljujemo ostatak pojacanja u krug kao pomoc svim napadima:
				int n=0;
				for(i=0;i<Toattack.size();i++)
					if(Attacktype.get(i)<=0)
						n++;
				int a=extraarmies/n;
				if(a>0)
					for(i=0;i<Toattack.size();i++)
						if(Attacktype.get(i)<=0)
						{   Tofortify1.add(Toattack.get(i));
							Tofortify2.add(a);
							extraarmies-=a;
							if(extraarmies==0)
								break;
						}
				if(extraarmies>0)
					for(i=0;i<Toattack.size();i++)
						if(Attacktype.get(i)<=0)
						{   Tofortify1.add(Toattack.get(i));
							Tofortify2.add(1);
							extraarmies-=1;
							if(extraarmies==0)
								break;
						}
			}
			else if(area.size()==game.getCountries().length)
			{   Tofortify1.addAll(minattackers);
				Tofortify2.addAll(minreinforcementsneeds);
				for(i=0;i<Tofortify1.size();i++)
					if(extraarmies<=0)
					{   Tofortify1.remove(i);
						Tofortify2.remove(i);
						i--;
					}
					else
						extraarmies-=Tofortify2.get(i);
			}
		}
		povratnavrednost[0]=Extraarmies-extraarmies;//kol'ko treba tenkova za napad
		//kako je u planu pisano da se tenkovi postavljaju u teritorijama koje nam na pocetku ne pripadaju, resavamo to:
		List<List<Country>> graf=new ArrayList<>();
		List<Country> lista;
		prvapetlja:
		for(i=0;i<Toattack.size();i++)
		{   if(Attacktype.get(i)>0)
				continue;
			Country attacker=Toattack.get(i);
			Country defender=Todefend.get(i);
			drugapetlja:
			for(j=0;j<graf.size();j++)
				if(graf.get(j).contains(attacker))
				{   graf.get(j).add(defender);
					continue prvapetlja;
				}
			lista=new ArrayList<>();
			lista.add(attacker);
			lista.add(defender);
			graf.add(lista);
		}
		for(i=0;i<Tofortify1.size();i++)
		{   Country attacker=Tofortify1.get(i);
			for(j=0;j<graf.size();j++)
				if(graf.get(j).contains(attacker))
				{   Tofortify1.set(i,graf.get(j).get(0));
					break;
				}
		}
		povratnavrednost[1]=getReinforcements(cplayer);
		//vracanje izmenjenih podataka o teritorijama na staro:
		for(i=0;i<game.getCountries().length;i++)
		{   Country country=game.getCountries()[i];
			int Armies=armies[i];
			country.getOwner().getTerritoriesOwned().remove(country);
			country.setOwner(owners.get(i));
			owners.get(i).getTerritoriesOwned().add(country);
			country.removeArmies(country.getArmies());
			country.addArmies(Armies);
		}
		game.getPlayers().clear();
		game.getPlayers().addAll(players);
		povratnavrednost[1]-=getReinforcements(cplayer);//kol'ko ce da bude vece pojacanje ako plan uspe
		return povratnavrednost;
	}

	//pomocne funkcije
	private double[] SumOfDistances()
	{   int l=game.getCountries().length,i,j;
		double max=0;
		double[] distances=new double[l+1];
		int[] visited=new int[l+1];
		List<Integer> Distance;
		List<Country> countries;
		for(i=0;i<l;i++)
		{   Distance=new ArrayList<>();
			countries=new ArrayList<>();
			countries.add(game.getCountries()[i]);
			for(j=0;j<=l;j++)
				visited[j]=0;
			for(Country border:countries)
			{   visited[border.getColor()]=1;
				Distance.add(0);
			}
			for(j=0;j<countries.size();j++)
			{   Country country=countries.get(j);
				List<Country> neighbours;
				neighbours=country.getNeighbours();
				for(Country neighbour:neighbours)
					if(visited[neighbour.getColor()]==0)
					{   visited[neighbour.getColor()]=1;
						countries.add(neighbour);
						Distance.add(Distance.get(countries.indexOf(country))+1);
					}
			}
			for(j=0;j<Distance.size();j++)
				distances[i]+=Distance.get(j);
			if(max<distances[i])
			max=distances[i];
		}
		for(i=0;i<l;i++)
			distances[i]/=max;
		//ispisivanje mere rastojanja na karti:
		/*for(i=0;i<l;i++)
		{   Country country=game.getCountries()[i];
			country.removeArmies(country.getArmies());
			country.addArmies((int)(100*distances[i]));
		}*/
		return distances;
	}

	//Funkcija ce da vrati listu borders po referenci.
	/**
	 * If type is "outer", returns only not full defended countries.
	 * If type is "inner", border country can be full defended country if it has enough power.
	   See code for specific number.
	 * @param playerid is ordinal of player
	 */
	private List<Country> FindBorders(List<Country> borders,Player player, String type)
	{   List<Country> visited;
		List<Country> borders1=new ArrayList<>();
		visited=new ArrayList<>();
		visited.addAll(borders);
		//for(int i=0;i<=game.getCountries().length;i++)
		//    visited[i]=0;
		//for(Country border:borders)
		//    visited[border.getColor()]=1;

		//za manju granicu:
		for(int i=0;i<borders.size();i++)
		{   Country border=borders.get(i);
			HashSet<Country> neighbours=new HashSet<>();
			HashSet<Country> Neighbours=new HashSet<>();
			neighbours.addAll(border.getIncomingNeighbours());
			if(type.equals("outer"))
				neighbours.addAll(border.getNeighbours());
			Neighbours.addAll(neighbours);
			//Neighbours.removeAll(borders);
			Neighbours.removeAll(visited);
			//neighbours.removeAll(player.getTerritoriesOwned());
			neighbours=removeAll(player,neighbours);
			if(type.equals("outer")||type.equals("incoming outer"))
			{   if(!Neighbours.isEmpty()&&neighbours.isEmpty())
				{   borders.addAll(Neighbours);
					visited.addAll(Neighbours);
					visited.remove(border);
					visited.add(border);
				}
				if(neighbours.isEmpty())
				{   borders.remove(border);
					i--;
				}
			}
			else 
				if(border.getArmies()<6+game.getCountries().length/40&&neighbours.isEmpty())
					{   borders.addAll(Neighbours);
						borders.remove(border);
						i--;
						visited.addAll(Neighbours);
						visited.remove(border);
						visited.add(border);
					}
		}
		borders1.addAll(borders);

		//za vecu granicu:
		if(type.equals("outer"))
		for(int i=0;i<borders1.size();i++)
		{   Country border=borders1.get(i);
			HashSet<Country> neighbours=new HashSet<>();
			HashSet<Country> Neighbours=new HashSet<>();
			neighbours.addAll(border.getIncomingNeighbours());
			neighbours.addAll(border.getNeighbours());
			Neighbours.addAll(neighbours);
			//Neighbours.removeAll(borders);
			Neighbours.removeAll(visited);
			//Neighbours.retainAll(player.getTerritoriesOwned());
			Neighbours=retainAll(player,Neighbours);
			//neighbours.removeAll(player.getTerritoriesOwned());
			neighbours=removeAll(player,neighbours);
			if(!Neighbours.isEmpty())
			{   borders1.addAll(Neighbours);
				visited.addAll(Neighbours);
				visited.remove(border);
				visited.add(border);
			}
			if(neighbours.isEmpty())
			{   borders1.remove(border);
				i--;
			}
		}
		return borders1;
	}

	/**
	 * Returns all player's countries which can't be attacked directly - full defended countries.
	 * @param playerid is ordinal of player
	 */
	private List<Country> FindFullDefended(Player player)
	{   List<Country> fulldefended=new ArrayList<>();
		List<Country> countries=new ArrayList<>();
		countries.addAll(player.getTerritoriesOwned());
		prvapetlja:
		for(Country country:countries)
		{   HashSet<Country> neighbours=new HashSet<>();
			neighbours.addAll(country.getIncomingNeighbours());
			//neighbours.removeAll(player.getTerritoriesOwned());
			neighbours=removeAll(player,neighbours);
			if(neighbours.isEmpty())
			{   fulldefended.add(country);
				continue;
			}
			//ako skoro sve teritorije koje jednosmerno napadaju napadaju i sve susede, ali ne drzimo ih sve:
			if(!onewayattacked.contains(country))
				continue;
			neighbours=new HashSet<>();
			neighbours.addAll(country.getNeighbours());
			//neighbours.removeAll(player.getTerritoriesOwned());
			neighbours=removeAll(player,neighbours);
			if(!neighbours.isEmpty())
				continue;
			HashSet<Country> attackers=new HashSet<>();
			neighbours=new HashSet<>();
			HashSet<Country> ourneighbours=new HashSet<>();
			attackers.addAll(onewayattackers);
			attackers.retainAll(country.getIncomingNeighbours());
			attackers.removeAll(country.getNeighbours());
			//attackers.removeAll(player.getTerritoriesOwned());
			attackers=removeAll(player,attackers);
			neighbours.addAll(country.getNeighbours());
			ourneighbours.addAll(neighbours);
			//ourneighbours.retainAll(player.getTerritoriesOwned());
			ourneighbours=retainAll(player,ourneighbours);
			if(neighbours.size()==ourneighbours.size())
				continue;
			for(Country onewayattacker:attackers)
			{   HashSet<Country> neighbours1=new HashSet<>();
				neighbours1.addAll(neighbours);
				neighbours1.removeAll(onewayattacker.getNeighbours());
				if(neighbours1.isEmpty())
					fulldefended.add(country);
			}
		}
		return fulldefended;
	}

	/**
	 * Returns all continents which 'player' own.
	 */
	private HashSet<Continent> getContinentsOwned(Player player)
	{   Continent[] continents=game.getContinents();
		HashSet<Continent> ContinentsOwned=new HashSet<>();
		for(Continent continent:continents)
		{   List<Country> countries=continent.getTerritoriesContained();
			int ind=0;
			for(Country country:countries)
				if(country.getOwner()!=player)
				{   ind=1;
					break;
				}
			if(ind==0)
				ContinentsOwned.add(continent);
		}
		return ContinentsOwned;
	}

	private double[] FindThreats(Player player)
	{   //odakle cemo gledati pretnje
		Country[] territories=game.getCountries();
		double[] threats=new double[territories.length+1];
		double[] threats1;
		//List<Country> betterdefence=new ArrayList<>(),worsedefence=new ArrayList<>();
		//FindDefensible(betterdefence,worsedefence,player);
		List<Country> countries=new ArrayList<>();
		countries.addAll(player.getTerritoriesOwned());
		List<Country> from=new ArrayList<>();
		List<Country> to;
		while(!countries.isEmpty())
		{   Country country=countries.get(0);
			if((worsedefence.contains(country)||betterdefence.contains(country))&&threats[country.getColor()]==0)
			{   int i=0;
				to=new ArrayList<>();
				to.add(country);
				for(;i<to.size();i++)
				{   Country From=to.get(i);
					HashSet<Country> neighbours=new HashSet<>();
					neighbours.addAll(From.getNeighbours());
					neighbours.addAll(From.getIncomingNeighbours());
					//neighbours.retainAll(player.getTerritoriesOwned());
					neighbours=retainAll(player,neighbours);
					for(Country neighbour:neighbours)
					{   if((worsedefence.contains(neighbour)||betterdefence.contains(neighbour))&&!to.contains(neighbour))
							to.add(neighbour);
					}
				}
				from.addAll(to);
				countries.removeAll(to);
				if(!from.isEmpty())
					from=TerritoriesOnDistance(from,-4-game.getCountries().length/50,"all");
				for(int j=0;j<from.size();j++)
				{   Country From=from.get(j);
					if(From.getOwner()==player)
						from.remove(From);
				}
				threats1=FindThreats(from,to,player);
				int l=game.getCountries().length;
				for(i=1;i<=l;i++)
					threats[i]=Math.max(threats1[i],threats[i]);
			}
			else
			{   threats[country.getColor()]=FindThreats(player,country,null);
				countries.remove(0);
			}
		}
		return threats;
	}

	/**
	 * Returns sequence of threats from 'from' to each country.
	 * @param player is player for whom we are searching threats 
	 */
	private double[] FindThreats(List<Country> from, List<Country> to, Player player)
	{   List<Country> countries=new ArrayList<>();
		Country[] territories=game.getCountries();
		int i;
		int l=game.getCountries().length;
		double[] threats=new double[territories.length+1];
		Player[] occupier=new Player[territories.length+1];
		double[] reinforcements=new double[game.getPlayers().size()];
		for(i=0;i<game.getPlayers().size();i++)
			reinforcements[i]=getReinforcements((Player)game.getPlayers().get(i));
		for(i=0;i<territories.length;i++)
		{   Country territory=territories[i];
			occupier[i+1]=territory.getOwner();
			if(territory.getOwner()!=player&&from.contains(territory))
			{   countries.add(territory);
				//threats[i+1]=territory.getArmies()+getReinforcements(territory.getOwner());
				threats[i+1]=territory.getArmies()+reinforcements[game.getPlayers().indexOf(territory.getOwner())];
				if(betterdefence.contains(territory)||almostconquered.contains(territory.getContinent()))
				{   HashSet<Country> neighbours=new HashSet<>();
					neighbours.addAll(territory.getIncomingNeighbours());
					//neighbours.removeAll(territory.getOwner().getTerritoriesOwned());
					neighbours=removeAll(territory.getOwner(),neighbours);
					double max=6;
					for(Country neighbour:neighbours)
						if(!to.contains(neighbour)&&neighbour.getArmies()+reinforcements[game.getPlayers().indexOf(neighbour.getOwner())]-3>max)
							max=neighbour.getArmies()+reinforcements[game.getPlayers().indexOf(neighbour.getOwner())]-3;
					threats[i+1]-=max*2/3+3;
				}
			}
			else
				threats[i+1]=0;
		}
		while(!countries.isEmpty())
		{   Country country=countries.get(0);
			HashSet<Country> neighbours=new HashSet<>();
			neighbours.addAll(country.getNeighbours());
			for(Country neighbour:neighbours)
			{   if(neighbour.getOwner()==occupier[country.getColor()])
					continue;
				double attack,defence;
				attack=threats[country.getColor()]-1;
				defence=neighbour.getArmies();
				if(attack>3)
				if(to.contains(neighbour))
					threats[neighbour.getColor()]=attack-3;
				else if(attack-1.6*(Math.max(defence,1)-1)>threats[neighbour.getColor()])
				{   threats[neighbour.getColor()]=attack-1.6*(Math.max(defence,1)-1);
					countries.add(neighbour);
					occupier[neighbour.getColor()]=occupier[country.getColor()];
				}
			}
			countries.remove(country);
		}
		for(i=1;i<=l;i++)
			if(!to.contains(game.getCountries()[i-1]))
				threats[i]=0;
			else
				threats[i]/=1.6;

		List<Country> countryneighbours1=new ArrayList<>();
		for(Country country:to)
		{   countryneighbours1.removeAll(country.getIncomingNeighbours());
			countryneighbours1.addAll(country.getIncomingNeighbours());
		}
		countryneighbours1=removeAll(player,countryneighbours1);
		countryneighbours1.retainAll(from);
		double[] neighbourthreats=new double[countryneighbours1.size()];
		for(i=0;i<countryneighbours1.size();i++)
		{   Country neighbour=countryneighbours1.get(i);
			neighbourthreats[i]+=neighbour.getArmies()-3;
		}                

		for(int j=0;j<to.size();j++)
		{   int[] ind32=new int[RiskGame.MAX_PLAYERS];
			Country country=to.get(j);
			List<Country> countryneighbours=removeAll(player,country.getIncomingNeighbours());
			countryneighbours.retainAll(from);
			double[] countrythreats=new double[countryneighbours.size()];
			for(i=0;i<countryneighbours.size();i++)
			{   Country neighbour=countryneighbours.get(i);
				List<Country> Neighbours=removeAll(neighbour.getOwner(),neighbour.getNeighbours());
				if(Neighbours.isEmpty())
					continue;
				Country indmin=Neighbours.get(0);
				int indequal=0;
				for(Country country1:Neighbours)
				{   if(country1==indmin)
						continue;
					if(country1.getArmies()<indmin.getArmies())
					{   indmin=country1;
						indequal=0;
					}
					else if(country1.getArmies()==indmin.getArmies())
						indequal=1;
				}
				Continent continent=country.getContinent();
				//if(game.previousFulldefended.contains(country.getColor()))
				//    countrythreats[i]=neighbourthreats[countryneighbours1.indexOf(neighbour)]*3/2;
				if(almostconquered.contains(continent)&&!betterdefence.contains(country)&&almostconqueredP.get(almostconquered.indexOf(continent))==neighbour.getOwner())
					countrythreats[i]=neighbourthreats[countryneighbours1.indexOf(neighbour)]*3/2;
				else if(!betterdefence.contains(country)&&country==indmin&&indequal==0&&country.getOwner()==player&&
					(betterdefence.contains(neighbour)||worsedefence.contains(neighbour)))
					countrythreats[i]=neighbourthreats[countryneighbours1.indexOf(neighbour)]*3/2;
				else
					countrythreats[i]=neighbourthreats[countryneighbours1.indexOf(neighbour)];

			}
			for(i=0;i<countryneighbours.size();i++)
			{   Country neighbour=countryneighbours.get(i);
				if(neighbour.getOwner()==player)
					continue;
				// <editor-fold defaultstate="collapsed">
				//ako country sprecava osvajanje kontinenta od vlasnika neighbour-a,
				//vazi uslovni betterdefence:
				/*Continent continent=country.getContinent();
				if(almostconquered.contains(continent)&&!betterdefence.contains(country)&&almostconqueredP.get(almostconquered.indexOf(continent))==neighbour.getOwner())
				{   countrythreats[countryneighbours.indexOf(neighbour)]=((double)neighbour.getArmies()-3)*3/2;
					ind32[game.getPlayers().indexOf(neighbour.getOwner())]=1;
				}
				//isto ako neighbour može da napadne samo country ili je country najslabiji (u slabijem smislu) od svih suseda:
				else if(!betterdefence.contains(country))
				{   int ind=0;
					HashSet<Country> Neighbours=new HashSet<>();
					Neighbours.addAll(neighbour.getNeighbours());
					//Neighbours.removeAll(neighbour.getOwner().getTerritoriesOwned());
					Neighbours=removeAll(neighbour.getOwner(),Neighbours);
					Neighbours.remove(country);
					if(Neighbours.isEmpty())
						ind=1;
					if(ind==0)
					{   int min=country.getArmies();
						ind=1;
						for(Country Neighbour:Neighbours)
							if(Neighbour.getArmies()<min+1)
							{   ind=0;
								break;
							}
					}
					if(ind==1)
					{   countrythreats[countryneighbours.indexOf(neighbour)]=((double)neighbour.getArmies()-3)*3/2;
						ind32[game.getPlayers().indexOf(neighbour.getOwner())]=1;
					}
				}*/
				// </editor-fold>
				HashSet<Country> Neighbours=new HashSet<>();
				Neighbours.addAll(neighbour.getIncomingNeighbours());
				//Neighbours.removeAll(neighbour.getOwner().getTerritoriesOwned());
				Neighbours=removeAll(neighbour.getOwner(),Neighbours);
				//pretnja ima svoje pretnje, pa je zapravo manja:
				int ind=0;
				if(country.getOwner()!=player||extendedworsedefence.contains(country)||(!betterdefence.contains(country)&&!worsedefence.contains(country)))
				for(int k=0;k<almostconquered.size();k++)
				{   Continent continent1=almostconquered.get(k);
					if(continent1==neighbour.getContinent())
						if(player==almostconqueredP.get(k))
							ind=1;
						else
						{   ind=0;
							break;
						}
				}
				if((betterdefence.contains(neighbour)||(worsedefence.contains(neighbour)&&!extendedworsedefence.contains(neighbour))||ind==1)&&Neighbours.size()>1)
				if(!betterdefence.contains(country)||(betterdefence.contains(country)&&betterdefence.contains(neighbour))/*||smallmap==0*/)
				{   HashSet<Country> neighbours=new HashSet<>();
					neighbours.addAll(neighbour.getIncomingNeighbours());
					//neighbours.removeAll(neighbour.getOwner().getTerritoriesOwned());
					neighbours=removeAll(neighbour.getOwner(),neighbours);
					neighbours.remove(country);
					if(!betterdefence.contains(neighbour))
						//neighbours.retainAll(player.getTerritoriesOwned());
						neighbours=retainAll(player,neighbours);
					double max;
					if(betterdefence.contains(neighbour)||ind==1)
						max=6;
					else
						max=0;
					for(Country neighbour1:neighbours)
					{   //i pretnja pretnji moze imati pretnje, pa dolazi do ponistavanja u slucaju istog igraca:
						HashSet<Country> neighbours1=new HashSet<>();
						neighbours1.addAll(neighbour1.getIncomingNeighbours());
						neighbours1.remove(country);
						neighbours1.remove(neighbour);
						//neighbours1.retainAll(neighbour.getOwner().getTerritoriesOwned());
						neighbours1=retainAll(neighbour.getOwner(),neighbours1);
						double max1;
						if(betterdefence.contains(neighbour1))
							max1=6;
						else
							max1=0;
						for(Country neighbour2:neighbours1)
							if(neighbour2.getOwner()!=neighbour1.getOwner()&&neighbour2.getArmies()-3>max1)
								max1=neighbour2.getArmies()-3;
						if(neighbour1.getOwner()!=neighbour.getOwner()&&neighbour1.getArmies()-3-max1*2/3>0)
							max+=neighbour1.getArmies()-3-max1*2/3;
					}
					if(max>0)
						countrythreats[countryneighbours.indexOf(neighbour)]-=max/2;
					if(countrythreats[countryneighbours.indexOf(neighbour)]<0)
						countrythreats[countryneighbours.indexOf(neighbour)]=0;
				}
				else if(betterdefence.contains(neighbour)||ind==1)
					if(neighbour.getArmies()<=6)
						countrythreats[countryneighbours.indexOf(neighbour)]-=neighbour.getArmies();
					else
						countrythreats[countryneighbours.indexOf(neighbour)]-=6;
			}
			double threatsperplayers[]=new double[game.getPlayers().size()];
			for(Country neighbour:countryneighbours)
				threatsperplayers[game.getPlayers().indexOf(neighbour.getOwner())]=1;
			threatsperplayers[game.getPlayers().indexOf(player)]=0;
			for(i=0;i<game.getPlayers().size();i++)
				threatsperplayers[i]=threatsperplayers[i]*reinforcements[i];
			for(i=0;i<countryneighbours.size();i++)
			{   Country neighbour=countryneighbours.get(i);
				if(countrythreats[i]>0)
					threatsperplayers[game.getPlayers().indexOf(neighbour.getOwner())]+=countrythreats[i];
			}
			for(i=0;i<game.getPlayers().size();i++)
			{   if(threatsperplayers[i]<0)
					threatsperplayers[i]=0;
				else if(ind32[i]==1)
					threatsperplayers[i]+=reinforcements[i]/2;
			}
			for(i=0;i<game.getPlayers().size();i++)
				if(threatsperplayers[i]>threats[country.getColor()])
					threats[country.getColor()]=threatsperplayers[i];
			threats[country.getColor()]/=1.6;
		}
		return threats;
	}

	/**
	 * Returns threat to country 'country'.
	 * @param player is player for whom we are searching threats 
	 * @param defend can be used if we are searching for threats to country 'country', but we want to attack 'defend'.
	 */
	private double FindThreats(Player player, Country country, Country defend)
	{   //odakle cemo gledati pretnje
		//List<Country> Betterdefence=new ArrayList<>(),Worsedefence=new ArrayList<>();
		//FindDefensible(Betterdefence,Worsedefence,player);
		List<Country> countries;
		List<Country> from=new ArrayList<>();
		List<Country> from1;
		from.add(country);
		if((worsedefence.contains(country)||betterdefence.contains(country)))
		{   int i=0;
			for(;i<from.size();i++)
			{   Country From=from.get(i);
				HashSet<Country> neighbours=new HashSet<>();
				neighbours.addAll(From.getNeighbours());
				neighbours.addAll(From.getIncomingNeighbours());
				for(Country neighbour:neighbours)
				{   if((worsedefence.contains(neighbour)||betterdefence.contains(neighbour))&&!from.contains(neighbour)&&neighbour.getOwner()==player)
						from.add(neighbour);
				}
			}
		}
		from1=TerritoriesOnDistance(from,-1,"all");
		if(betterdefence.contains(country))
			from=TerritoriesOnDistance(from,-3-game.getCountries().length/50,"all");
		else
			from=TerritoriesOnDistance(from,-2-game.getCountries().length/75,"all");
		from.removeAll(from1);
		//from.removeAll(player.getTerritoriesOwned());
		from=removeAll(player,from);
		//racunanje pretnji
		countries=new ArrayList<>();
		Country[] territories=game.getCountries();
		int i;
		double[] Threats=new double[territories.length+1];
		double threat=0;
		Player[] occupier=new Player[territories.length+1];
		double[] reinforcements=new double[game.getPlayers().size()];
		for(i=0;i<game.getPlayers().size();i++)
			reinforcements[i]=getReinforcements((Player)game.getPlayers().get(i));
		for(i=0;i<territories.length;i++)
		{   Country territory=territories[i];
			occupier[i+1]=territory.getOwner();
			if(territory.getOwner()!=player&&from.contains(territory)&&territory!=defend)
			{   countries.add(territory);
				Threats[i+1]=territory.getArmies()+reinforcements[game.getPlayers().indexOf(territory.getOwner())];
				if(betterdefence.contains(territory)||almostconquered.contains(territory.getContinent()))
					Threats[i+1]-=threats[territory.getColor()]*2/3;
			}
			else
				Threats[i+1]=0;
		}
		HashSet<Country> neighbours;
		while(!countries.isEmpty())
		{   Country ccountry=countries.get(0);
			neighbours=new HashSet<>();
			neighbours.addAll(ccountry.getNeighbours());
			for(Country neighbour:neighbours)
			{   if(neighbour.getOwner()==occupier[ccountry.getColor()]&&neighbour!=country)
					continue;
				if(neighbour==defend)
					continue;
				double attack,defence;
				attack=Threats[ccountry.getColor()]-1;
				defence=neighbour.getArmies();
				if(attack>3)
				if(neighbour==country)
				{   if(attack-1>threat)
						threat=attack-1;
				}
				else if(attack-1.6*(Math.max(defence,1)-1)>Threats[neighbour.getColor()])
				{   Threats[neighbour.getColor()]=attack-1.6*(Math.max(defence,1)-1);
					countries.add(neighbour);
					if(neighbour==game.getCountryInt(94))
						;
					occupier[neighbour.getColor()]=occupier[ccountry.getColor()];
				}
			}
			countries.remove(ccountry);
		}

		int[] ind32=new int[RiskGame.MAX_PLAYERS];
		List<Country> countryneighbours=new ArrayList<>();
		countryneighbours.addAll(country.getIncomingNeighbours());
		//countryneighbours.removeAll(player.getTerritoriesOwned());
		countryneighbours=removeAll(player,countryneighbours);
		countryneighbours.remove(defend);
		double[] countrythreats=new double[countryneighbours.size()];
		for(i=0;i<countryneighbours.size();i++)
		{   Country neighbour=countryneighbours.get(i);
			List<Country> Neighbours=removeAll(neighbour.getOwner(),neighbour.getNeighbours());
			if(Neighbours.isEmpty())
				continue;
			Country indmin=Neighbours.get(0);
			int indequal=0;
			for(Country country1:Neighbours)
			{   if(country1==indmin)
					continue;
				if(country1.getArmies()<indmin.getArmies())
				{   indmin=country1;
					indequal=0;
				}
				else if(country1.getArmies()==indmin.getArmies())
					indequal=1;
			}
			Continent continent=country.getContinent();
			if(almostconquered.contains(continent)&&!betterdefence.contains(country)&&almostconqueredP.get(almostconquered.indexOf(continent))==neighbour.getOwner())
				countrythreats[i]+=(neighbour.getArmies()-3.0)*3/2;
			else if(!betterdefence.contains(country)&&country==indmin&&indequal==0&&
					(betterdefence.contains(neighbour)||worsedefence.contains(neighbour)))
				countrythreats[i]+=(neighbour.getArmies()-3.0)*3/2;
			else
				countrythreats[i]+=neighbour.getArmies()-3;
		}

		for(i=0;i<countryneighbours.size();i++)
		{   Country neighbour=countryneighbours.get(i);
			if(neighbour.getOwner()==player||neighbour==defend)
				continue;
			//ako country sprecava osvajanje kontinenta od vlasnika neighbour-a, vazi uslovni betterdefence:
			Continent continent=country.getContinent();
			if(almostconquered.contains(continent)&&!betterdefence.contains(country)&&almostconqueredP.get(almostconquered.indexOf(continent))==neighbour.getOwner())
			{   countrythreats[countryneighbours.indexOf(neighbour)]=((double)neighbour.getArmies()-3)*3/2;
				ind32[game.getPlayers().indexOf(neighbour.getOwner())]=1;
			}
			//isto ako neighbour može da napadne samo country ili je country najslabiji (u slabijem smislu) od svih suseda:
			else if(!betterdefence.contains(country)||(betterdefence.contains(country)&&betterdefence.contains(neighbour)))
			{   int ind=0;
				HashSet<Country> Neighbours=new HashSet<>();
				Neighbours.addAll(neighbour.getNeighbours());
				//Neighbours.removeAll(neighbour.getOwner().getTerritoriesOwned());
				Neighbours=removeAll(neighbour.getOwner(),Neighbours);
				Neighbours.remove(country);
				if(Neighbours.isEmpty())
					ind=1;
				if(ind==0)
				{   int min=country.getArmies();
					ind=1;
					for(Country Neighbour:Neighbours)
						if(Neighbour.getArmies()<min+1)
						{   ind=0;
							break;
						}
				}
				if(ind==1&&(betterdefence.contains(neighbour)||worsedefence.contains(neighbour)||fulldefended.contains(neighbour)))
				{   countrythreats[countryneighbours.indexOf(neighbour)]=((double)neighbour.getArmies()-3)*3/2;
					ind32[game.getPlayers().indexOf(neighbour.getOwner())]=1;
				}
			}
			//pretnja ima svoje pretnje, pa je zapravo manja:
			int ind=0;
			if(country.getOwner()!=player||extendedworsedefence.contains(country)||(!betterdefence.contains(country)&&!worsedefence.contains(country)))
			for(int k=0;k<almostconquered.size();k++)
			{   Continent continent1=almostconquered.get(k);
				if(continent1==neighbour.getContinent())
					if(player==almostconqueredP.get(k))
						ind=1;
					else
					{   ind=0;
						break;
					}
			}
			if(betterdefence.contains(neighbour)||(worsedefence.contains(neighbour)&&!extendedworsedefence.contains(neighbour))||ind==1)
			if(!betterdefence.contains(country)/*||smallmap==0*/)
			{   neighbours=new HashSet<>();
				neighbours.addAll(neighbour.getIncomingNeighbours());
				//neighbours.removeAll(neighbour.getOwner().getTerritoriesOwned());
				neighbours=removeAll(neighbour.getOwner(),neighbours);
				neighbours.remove(country);
				if(!betterdefence.contains(neighbour))
					//neighbours.retainAll(player.getTerritoriesOwned());
					neighbours=retainAll(player,neighbours);
				double max;
				if(betterdefence.contains(neighbour)||ind==1)
					max=6;
				else
					max=0;
				for(Country neighbour1:neighbours)
				{   //i pretnja pretnji moze imati pretnje, pa dolazi do ponistavanja u slucaju istog igraca:
					HashSet<Country> neighbours1=new HashSet<>();
					neighbours1.addAll(neighbour1.getIncomingNeighbours());
					neighbours1.remove(country);
					neighbours1.remove(neighbour);
					//neighbours1.retainAll(neighbour.getOwner().getTerritoriesOwned());
					neighbours1=retainAll(neighbour.getOwner(),neighbours1);
					double max1;
					if(betterdefence.contains(neighbour1))
						max1=6;
					else
						max1=0;
					for(Country neighbour2:neighbours1)
						if(neighbour2.getOwner()!=neighbour1.getOwner()&&neighbour2.getArmies()-3>max1)
							max1=neighbour2.getArmies()-3;
					if(neighbour1.getOwner()!=neighbour.getOwner()&&neighbour1.getArmies()-3-max1*2/3>0)
						max+=neighbour1.getArmies()-3-max1*2/3;
				}
				if(max>0)
					countrythreats[countryneighbours.indexOf(neighbour)]-=max/2;
				if(countrythreats[countryneighbours.indexOf(neighbour)]<0)
					countrythreats[countryneighbours.indexOf(neighbour)]=0;
			}
			else if(betterdefence.contains(neighbour)||ind==1)
				if(neighbour.getArmies()<=6)
					countrythreats[countryneighbours.indexOf(neighbour)]-=neighbour.getArmies();
				else
					countrythreats[countryneighbours.indexOf(neighbour)]-=6;
		}
		double threatsperplayers[]=new double[game.getPlayers().size()];
		for(Country neighbour:countryneighbours)
			if(neighbour!=defend)
				threatsperplayers[game.getPlayers().indexOf(neighbour.getOwner())]=1;
		threatsperplayers[game.getPlayers().indexOf(player)]=0;
		for(i=0;i<game.getPlayers().size();i++)
			threatsperplayers[i]=threatsperplayers[i]*reinforcements[i];
		for(i=0;i<countryneighbours.size();i++)
		{   Country neighbour=countryneighbours.get(i);
			if(countrythreats[i]>0)
				threatsperplayers[game.getPlayers().indexOf(neighbour.getOwner())]+=countrythreats[i];
		}
		for(i=0;i<game.getPlayers().size();i++)
		{   if(threatsperplayers[i]<0)
				threatsperplayers[i]=0;
			  else if(ind32[i]==1)
				threatsperplayers[i]+=reinforcements[i]/2;
			if(threatsperplayers[i]>threat)
				threat=threatsperplayers[i];
		}
		threat/=1.6;
		if(threat<0)
			threat=0;
		return threat;
	}

	/**
	 * Returns threat to country 'country'.
	 * @param player is player for whom we are searching threats 
	 * This is more general case of upper function for all neighbors.
	 */
	private List<Double> FindThreats(Player player, Country country)
	{   //odakle cemo gledati pretnje
		//List<Country> Betterdefence=new ArrayList<>(),Worsedefence=new ArrayList<>();
		//FindDefensible(Betterdefence,Worsedefence,player);
		List<Country> countries;
		List<Country> from=new ArrayList<>();
		List<Country> from1;
		from.add(country);
		if((worsedefence.contains(country)||betterdefence.contains(country)))
		{   int i=0;
			for(;i<from.size();i++)
			{   Country From=from.get(i);
				HashSet<Country> neighbours=new HashSet<>();
				neighbours.addAll(From.getNeighbours());
				neighbours.addAll(From.getIncomingNeighbours());
				for(Country neighbour:neighbours)
				{   if((worsedefence.contains(neighbour)||betterdefence.contains(neighbour))&&!from.contains(neighbour)&&neighbour.getOwner()==player)
						from.add(neighbour);
				}
			}
		}
		from1=TerritoriesOnDistance(from,-1,"all");
		if(betterdefence.contains(country))
			from=TerritoriesOnDistance(from,-3-game.getCountries().length/50,"all");
		else
			from=TerritoriesOnDistance(from,-2-game.getCountries().length/75,"all");
		from.removeAll(from1);
		//from.removeAll(player.getTerritoriesOwned());
		from=removeAll(player,from);
		//racunanje pretnji
		countries=new ArrayList<>();
		Country[] territories=game.getCountries();
		int i;
		double[] Threats=new double[territories.length+1];
		double threat1=0;
		Player[] occupier=new Player[territories.length+1];
		double[] reinforcements=new double[game.getPlayers().size()];
		for(i=0;i<game.getPlayers().size();i++)
			reinforcements[i]=getReinforcements((Player)game.getPlayers().get(i));
		for(i=0;i<territories.length;i++)
		{   Country territory=territories[i];
			occupier[i+1]=territory.getOwner();
			if(territory.getOwner()!=player&&from.contains(territory))
			{   countries.add(territory);
				Threats[i+1]=territory.getArmies()+reinforcements[game.getPlayers().indexOf(territory.getOwner())];
				if(betterdefence.contains(territory)||almostconquered.contains(territory.getContinent()))
					Threats[i+1]-=threats[territory.getColor()]*2/3;
			}
			else
				Threats[i+1]=0;
		}
		HashSet<Country> neighbours;
		while(!countries.isEmpty())
		{   Country ccountry=countries.get(0);
			neighbours=new HashSet<>();
			neighbours.addAll(ccountry.getNeighbours());
			for(Country neighbour:neighbours)
			{   if(neighbour.getOwner()==occupier[ccountry.getColor()]&&neighbour!=country)
					continue;
				double attack,defence;
				attack=Threats[ccountry.getColor()]-1;
				defence=neighbour.getArmies();
				if(attack>3)
				if(neighbour==country)
				{   if(attack-1>threat1)
						threat1=attack-1;
				}
				else if(attack-1.6*(Math.max(defence,1)-1)>Threats[neighbour.getColor()])
				{   Threats[neighbour.getColor()]=attack-1.6*(Math.max(defence,1)-1);
					countries.add(neighbour);
					occupier[neighbour.getColor()]=occupier[ccountry.getColor()];
				}
			}
			countries.remove(ccountry);
		}

		List<Country> defenders=country.getNeighbours();
		List<Double> threats=new ArrayList<>();
		for(Country defend:defenders)
		{   if(defend.getOwner()==player)
			{   threats.add(0.0);
				continue;
			}
			int[] ind32=new int[RiskGame.MAX_PLAYERS];
			double threat=threat1;
			List<Country> countryneighbours=new ArrayList<>();
			countryneighbours.addAll(country.getIncomingNeighbours());
			//countryneighbours.removeAll(player.getTerritoriesOwned());
			countryneighbours=removeAll(player,countryneighbours);
			double[] countrythreats=new double[countryneighbours.size()];
			for(i=0;i<countryneighbours.size();i++)
			{   Country neighbour=countryneighbours.get(i);
				List<Country> Neighbours=removeAll(neighbour.getOwner(),neighbour.getNeighbours());
				if(Neighbours.isEmpty())
					continue;
				Country indmin=Neighbours.get(0);
				int indequal=0;
				for(Country country1:Neighbours)
				{   if(country1==indmin)
						continue;
					if(country1.getArmies()<indmin.getArmies())
					{   indmin=country1;
						indequal=0;
					}
					else if(country1.getArmies()==indmin.getArmies())
						indequal=1;
				}
				Continent continent=country.getContinent();
				if(almostconquered.contains(continent)&&!betterdefence.contains(country)&&almostconqueredP.get(almostconquered.indexOf(continent))==neighbour.getOwner())
					countrythreats[i]+=(neighbour.getArmies()-3.0)*3/2;
				else if(!betterdefence.contains(country)&&country==indmin&&indequal==0&&country.getOwner()==player&&
					(betterdefence.contains(neighbour)||worsedefence.contains(neighbour)))
					countrythreats[i]+=(neighbour.getArmies()-3.0)*3/2;
				else
					countrythreats[i]+=neighbour.getArmies()-3;
			}

			for(i=0;i<countryneighbours.size();i++)
			{   Country neighbour=countryneighbours.get(i);
				if(neighbour.getOwner()==player||neighbour==defend)
					continue;
				//ako country sprecava osvajanje kontinenta od vlasnika neighbour-a, vazi uslovni betterdefence:
				Continent continent=country.getContinent();
				if(almostconquered.contains(continent)&&!betterdefence.contains(country)&&almostconqueredP.get(almostconquered.indexOf(continent))==neighbour.getOwner())
				{   countrythreats[countryneighbours.indexOf(neighbour)]=((double)neighbour.getArmies()-3)*3/2;
					ind32[game.getPlayers().indexOf(neighbour.getOwner())]=1;
				}
				//isto ako neighbour može da napadne samo country ili je country najslabiji (u slabijem smislu) od svih suseda::
				else if(!betterdefence.contains(country)||(betterdefence.contains(country)&&betterdefence.contains(neighbour)))
				{   int ind=0;
					HashSet<Country> Neighbours=new HashSet<>();
					Neighbours.addAll(neighbour.getNeighbours());
					//Neighbours.removeAll(neighbour.getOwner().getTerritoriesOwned());
					Neighbours=removeAll(neighbour.getOwner(),Neighbours);
					Neighbours.remove(country);
					if(Neighbours.isEmpty())
						ind=1;
					if(ind==0)
					{   int min=country.getArmies();
						ind=1;
						for(Country Neighbour:Neighbours)
							if(Neighbour.getArmies()<min+1)
							{   ind=0;
								break;
							}
					}
					if(ind==1&&country.getOwner()==player&&(betterdefence.contains(neighbour)||worsedefence.contains(neighbour)))
					{   countrythreats[countryneighbours.indexOf(neighbour)]=((double)neighbour.getArmies()-3)*3/2;
						ind32[game.getPlayers().indexOf(neighbour.getOwner())]=1;
					}
				}
				//pretnja ima svoje pretnje, pa je zapravo manja:
				int ind=0;
				if(country.getOwner()!=player||extendedworsedefence.contains(country)||(!betterdefence.contains(country)&&!worsedefence.contains(country)))
				for(int k=0;k<almostconquered.size();k++)
				{   Continent continent1=almostconquered.get(k);
					if(continent1==neighbour.getContinent())
						if(player==almostconqueredP.get(k))
							ind=1;
						else
						{   ind=0;
							break;
						}
				}
				if(betterdefence.contains(neighbour)||(worsedefence.contains(neighbour)&&!extendedworsedefence.contains(neighbour))||ind==1)
				if(!betterdefence.contains(country)/*||smallmap==0*/)
				{   neighbours=new HashSet<>();
					neighbours.addAll(neighbour.getIncomingNeighbours());
					//neighbours.removeAll(neighbour.getOwner().getTerritoriesOwned());
					neighbours=removeAll(neighbour.getOwner(),neighbours);
					neighbours.remove(country);
					if(!betterdefence.contains(neighbour))
						//neighbours.retainAll(player.getTerritoriesOwned());
						neighbours=retainAll(player,neighbours);
					double max;
					if(betterdefence.contains(neighbour)||ind==1)
						max=6;
					else
						max=0;
					for(Country neighbour1:neighbours)
					{   //i pretnja pretnji moze imati pretnje, pa dolazi do ponistavanja u slucaju istog igraca:
						HashSet<Country> neighbours1=new HashSet<>();
						neighbours1.addAll(neighbour1.getIncomingNeighbours());
						neighbours1.remove(country);
						neighbours1.remove(neighbour);
						//neighbours1.retainAll(neighbour.getOwner().getTerritoriesOwned());
						neighbours1=retainAll(neighbour.getOwner(),neighbours1);
						double max1;
						if(betterdefence.contains(neighbour1)||ind==1)
							max1=6;
						else
							max1=0;
						for(Country neighbour2:neighbours1)
							if(neighbour2.getOwner()!=neighbour1.getOwner()&&neighbour2.getArmies()-3>max1)
								max1=neighbour2.getArmies()-3;
						if(neighbour1.getOwner()!=neighbour.getOwner()&&neighbour1.getArmies()-3-max1*2/3>0)
							max+=neighbour1.getArmies()-3-max1*2/3;
					}
					if(max>0)
						countrythreats[countryneighbours.indexOf(neighbour)]-=max/2;
					if(countrythreats[countryneighbours.indexOf(neighbour)]<0)
						countrythreats[countryneighbours.indexOf(neighbour)]=0;
				}
				else if(betterdefence.contains(neighbour))
					if(neighbour.getArmies()<=6)
						countrythreats[countryneighbours.indexOf(neighbour)]-=neighbour.getArmies();
					else
						countrythreats[countryneighbours.indexOf(neighbour)]-=6;
			}
			double threatsperplayers[]=new double[game.getPlayers().size()];
			for(Country neighbour:countryneighbours)
				if(neighbour!=defend)
					threatsperplayers[game.getPlayers().indexOf(neighbour.getOwner())]=1;
			threatsperplayers[game.getPlayers().indexOf(player)]=0;
			for(i=0;i<game.getPlayers().size();i++)
				threatsperplayers[i]=threatsperplayers[i]*reinforcements[i];
			for(i=0;i<countryneighbours.size();i++)
			{   Country neighbour=countryneighbours.get(i);
				if(countrythreats[i]>0)
					threatsperplayers[game.getPlayers().indexOf(neighbour.getOwner())]+=countrythreats[i];
			}
			for(i=0;i<game.getPlayers().size();i++)
			{   if(threatsperplayers[i]<0)
					threatsperplayers[i]=0;
				else if(ind32[i]==1)
					threatsperplayers[i]+=reinforcements[i]/2;
				if(threatsperplayers[i]>threat)
					threat=threatsperplayers[i];
			}
			threat/=1.6;
			if(threat<0)
				threat=0;
			threats.add(threat);
		}
		return threats;
	}

	/**
	 * If type is "max", returns all countries on distance 'distance' from 'countries'.
	 * If type is "all", returns all countries on distance less or equals 'distance' from 'countries'.
	 */
	private List<Country> TerritoriesOnDistance(List<Country> Countries,int distance, String type)
	{   int l=game.getCountries().length,i,ind=1;
		int[] visited=new int[l+1];
		if(distance<0)
		{   ind=-1;
			distance=0-distance;
		}
		List<Integer> Distance=new ArrayList<>();
		List<Country> countries=new ArrayList<>();
		countries.addAll(Countries);
		for(i=0;i<=l;i++)
			visited[i]=0;
		//try{
		for(Country border:countries)
		{   visited[border.getColor()]=1;
			Distance.add(0);
		}
		/*}catch(Exception e){
			l=l;
		}*/
		for(i=0;i<countries.size();i++)
		{   Country country=countries.get(i);
			if(Distance.get(countries.indexOf(country))==distance)
				return countries;
			HashSet<Country> neighbours=new HashSet<>();
			if(ind==1)
				neighbours.addAll(country.getNeighbours());
			else
				neighbours.addAll(country.getIncomingNeighbours());
			for(Country neighbour:neighbours)
				if(visited[neighbour.getColor()]==0)
				{   visited[neighbour.getColor()]=1;
					countries.add(neighbour);
					Distance.add(Distance.get(countries.indexOf(country))+1);
				}
			if("max".equals(type))
			{   countries.remove(i);
				Distance.remove(i);
				i--;
			}
		}
		return countries;
	}

	/**
	 * Returns player's reinforcements.
	 */
	private int getReinforcements(Player player)
	{   int reinforcements=0,cavalry=0,infantry=0,cannon=0,wildcard=0;
		if(player.getTerritoriesOwned().size()/3>3)
			reinforcements+=player.getTerritoriesOwned().size()/3;
		else
			reinforcements+=3;
		HashSet<Continent> continents=getContinentsOwned(player);
		for(Continent continent:continents)
			reinforcements+=continent.getArmyValue();
		// <editor-fold defaultstate="collapsed">
	 /*   List<Card> cards;
		cards=player.getCards();
		for(Card card:cards)
			if(card.getName().equals("Cavalry")) cavalry++;
			else if(card.getName().equals("Infantry")) infantry++;
			else if(card.getName().equals("Cannon")) cannon++;
			else wildcard++;
		while(cavalry>0&&infantry>0&&cannon>0)
		{   reinforcements+=game.getTradeAbsValue("Cavalry", "Infantry", "Cannon", 2);
			cavalry--;
			infantry--;
			cannon--;
		}
		while(wildcard>0&&(cavalry>1||infantry>1||cannon>1))
		{   reinforcements+=game.getTradeAbsValue("wildcard", "Infantry", "Infantry", 2);
			if(cavalry>infantry&&cavalry>cannon)
			{   wildcard--;
				cavalry-=2;
			}
			else if (infantry>cavalry&&infantry>cannon)
			{   wildcard--;
				infantry-=2;
			}
			else
			{   wildcard--;
				cannon-=2;
			}
		}
		while(cavalry>3)
		{   reinforcements+=game.getTradeAbsValue("Cavalry", "Cavalry", "Cavalry", 2);
			cavalry-=3;
		}
		while(infantry>3)
		{   reinforcements+=game.getTradeAbsValue("Infantry", "Infantry", "Infantry", 2);
			infantry-=3;
		}
		while(cannon>3)
		{   reinforcements+=game.getTradeAbsValue("Cannon", "Cannon", "Cannon", 2);
			cannon-=3;
		}*/
		// </editor-fold>
		return reinforcements;
	}

	private void FindDefensible(List<Country> betterdefence, List<Country> worsedefence, Player player)
	{   List<Country> fulldefended;
		List<Country> borders=new ArrayList<>();;
		//List<Country> fulldefended1=new ArrayList<>(),fulldefended2=new ArrayList<>();
		//List<Country> borders=new ArrayList<>()/*=FindFullDefended(playerid)*/;
		List<Country> countries;
		fulldefended=FindFullDefended(player);//unutrasnje teritorije
		worsedefence.addAll(fulldefended);
		FindBorders(worsedefence,player,"outer");//odbrambena granica
		borders.addAll(worsedefence);
		if(game.getCountries().length>100)
		{   countries=TerritoriesOnDistance(worsedefence,1,"all");
			//countries.retainAll(player.getTerritoriesOwned());
			countries=retainAll(player,countries);
			countries=TerritoriesOnDistance(countries,1,"all");
		}
		else
			countries=TerritoriesOnDistance(worsedefence,1,"all");
		//countries.retainAll(player.getTerritoriesOwned());
		countries=retainAll(player,countries);
		worsedefence.clear();
		worsedefence.addAll(countries);
		worsedefence.removeAll(fulldefended);
		//worsedefence.retainAll(player.getTerritoriesOwned());
		worsedefence=retainAll(player,worsedefence);
		worsedefence.removeAll(borders);
		worsedefence.addAll(borders);
		HashSet<Continent> continents=new HashSet<>();
		// <editor-fold defaultstate="collapsed">
		//Trazimo koje teritorije cemo pojacavati jace, a koje slabije:
		/*if(!fulldefended.isEmpty())
		{   //3) Gde je strogo vise granica nego njima cuvanih unutrasnjih, racunaju se i unutrasnji zidovi.
			//Medjutim, ovo ima smisla za veci broj unutrasnjih teritorija:
			fulldefended2.addAll(fulldefended);
			while(!fulldefended2.isEmpty())
			{   Country country=fulldefended2.get(0);
				borders.clear();
				borders.add(country);
				FindBorders(borders,player,"inner");
				fulldefended2.removeAll(borders);

				List<Country> neighbours;
				List<Country> Neighbours;
				fulldefended1.add(country);
				for(int i=0;i<fulldefended1.size();i++)
				{   Country country1=fulldefended1.get(i);
					neighbours=new ArrayList<>();
					neighbours.addAll(country1.getIncomingNeighbours());
					neighbours.removeAll(fulldefended1);
					neighbours.removeAll(borders);
					for(Country neighbour:neighbours)
					{   Neighbours=new ArrayList<>();
						int ind=0;
						Neighbours.addAll(neighbour.getIncomingNeighbours());
						Neighbours.removeAll(fulldefended1);
						Neighbours.removeAll(neighbours);
						for(Country Neighbour:Neighbours)
							if(neighbour.getOwner()!=Neighbour.getOwner())
							{   ind=1;
								break;
							}
						if(ind==0)
							fulldefended1.add(neighbour);
					}
				}
				fulldefended2.removeAll(fulldefended1);
				for(int i=0;i<borders.size();i++)
				{   Country terrirory=borders.get(i);
					if(fulldefended.contains(terrirory))
						borders.remove(i);
				}
				if(fulldefended1.size()>borders.size()&&fulldefended1.size()>5+game.getCountries().length/50)
					for(Country terrirory:borders)
					{   if(!betterdefence.contains(terrirory))
							betterdefence.add(terrirory);
						worsedefence.remove(terrirory);
					}
			}
		}*/
		// </editor-fold>
		//5) Ima li osvojenih kontinenata?
		betterdefence.clear();
		continents.clear();
		continents=getContinentsOwned(player);
		//Ima li na karti previse malih kontinenata?
		double averagevalue=0,averagesize=0;
		int count=0;
		for(Continent continent:game.getContinents())
			if(continent.getTerritoriesContained().size()>1)
			{   averagevalue+=continent.getArmyValue();
				averagesize+=continent.getTerritoriesContained().size();
				count++;
			}
		averagevalue=averagevalue/count;
		averagesize=averagesize/count;
		if(averagesize<4.5)
			for(Continent continent:game.getContinents())
				if(continent.getArmyValue()<averagevalue+2)
					continents.remove(continent);
		HashSet<Country> bordercountries=new HashSet<>();
		//4) Ima li teritorija koje napadaju jednosmerno puno teritorija?
		worsedefence.removeAll(multiattackers);
		for(Country multiattacker:multiattackers)
			if(!betterdefence.contains(multiattacker)&&!continents.contains(multiattacker.getContinent()))
				if(multiattacker.getOwner()==player)
					betterdefence.add(multiattacker);
		for(Continent continent:game.getContinents())
			bordercountries.addAll(continent.getIncomingBorderCountries());//ivice skoro svih kontinenata
		//preventivna odbrana skoro svakog kontinenta:
		HashSet<Country> CrossContinentNeighbours;
		HashSet<Country> oneenemyneighbours=new HashSet<>();
		for(Continent continent:continents)
		{   prvapetlja:
			for(Country country:(List<Country>)continent.getTerritoriesContained())
			{   if(betterdefence.contains(country))
					continue;
				CrossContinentNeighbours=new HashSet<>();
				CrossContinentNeighbours.addAll(country.getIncomingNeighbours());
				//CrossContinentNeighbours.removeAll(continent.getTerritoriesContained());
				CrossContinentNeighbours=removeAll(continent,CrossContinentNeighbours);
				if(CrossContinentNeighbours.isEmpty())
					continue;
				if(!fulldefended.contains(country))
				{   betterdefence.add(country);
					continue;
				}
				for(Country country1:CrossContinentNeighbours)
					if((country1.getArmies()<6+game.getCountries().length/85&&!betterdefence.contains(country1)&&country1.getArmies()<=country.getArmies())||worsedefence.contains(country1))
					{   betterdefence.remove(country);
						betterdefence.add(country);
						if(CrossContinentNeighbours.size()==1)
							oneenemyneighbours.add(country);
						continue prvapetlja;
					}
				betterdefence.addAll(CrossContinentNeighbours);
			}
		}
		HashSet<Country> neighbours;
		int ind;
		while(true)
		{   ind=0;
			//Izbacimo viskove koji nisu uoceni jer su ranije upisani:
			prvapetlja:
			for(int i=0;i<betterdefence.size();i++)
			{   Country country=betterdefence.get(i);
				if(!fulldefended.contains(country))
					continue;
				CrossContinentNeighbours=new HashSet<>();
				CrossContinentNeighbours.addAll(country.getIncomingNeighbours());
				//CrossContinentNeighbours.removeAll(country.getContinent().getTerritoriesContained());
				CrossContinentNeighbours=removeAll(country.getContinent(),CrossContinentNeighbours);
				if(CrossContinentNeighbours.isEmpty())
					continue;
				for(Country country1:CrossContinentNeighbours)
					if(!betterdefence.contains(country1))
						continue prvapetlja;
				betterdefence.remove(country);
				ind=1;
				i--;
			}
			//moze li se odbrana kontinenata pomeriti tako da bude manje teritorija:
			prvapetlja:
			for(Country country:bordercountries)
				if(!betterdefence.contains(country))
				{   neighbours=new HashSet<>();
					neighbours.addAll(country.getIncomingNeighbours());
					neighbours.retainAll(oneenemyneighbours);
					//neighbours.removeAll(country.getContinent().getTerritoriesContained());
					neighbours=removeAll(country.getContinent(),neighbours);
					int ind1=0;
					for(Country country1:neighbours)
						if(worsedefence.contains(country1))
							continue prvapetlja;
						else if(country1.getArmies()>=country.getArmies())
							ind1=1;
					if(neighbours.size()>1&&ind1==1)
					{   betterdefence.removeAll(neighbours);
						betterdefence.add(country);
						ind=1;
					}
				}
			if(ind==0)
				break;
		}
		//return;
	}

	private double[] FindPaths(Player player)
	{   int n=game.getCountries().length+1;
		double defense=0;
		double[] paths=new double[2*n];
		double[] threats=FindThreats(player);//Prvih n su tenkovi koji su potrebni za prelazak puta, drugih n su put.
		List<Country> borders=new ArrayList<>();
		FindBorders(borders,player,"outer");
		for(int i=0;i<n-1;i++)
			if(threats[i+1]>0)
				if(borders.contains(game.getCountries()[i]))
					paths[i+1]=threats[i+1]+3-game.getCountries()[i].getArmies();
				else
					paths[i+1]=3-game.getCountries()[i].getArmies();
		List<Country> countries=new ArrayList<>();
		countries.addAll(player.getTerritoriesOwned());
		while(!countries.isEmpty())
		{   Country country=countries.get(0);
			List<Country> neighbours=new ArrayList<>();
			neighbours.addAll(country.getNeighbours());
			for(Country neighbour:neighbours)
			{   if(neighbour.getOwner()==player)
					continue;
				defense=paths[country.getColor()];
				if(neighbour.getArmies()==1)
					defense+=1;
				else if(neighbour.getArmies()==2)
					defense+=1.7;
				else
					defense+=(neighbour.getArmies()-1)*1.5+1;
				if(defense<paths[neighbour.getColor()]||paths[neighbour.getColor()]==0)
				{   paths[neighbour.getColor()]=defense;
					paths[neighbour.getColor()+n]=country.getColor();
					if(!countries.contains(neighbour))
						countries.add(neighbour);
				}
			}
			countries.remove(country);
		}
		return paths;
	}

	/**
	 * Returns array that determinate best path to each country of continent.
	 * @param type is:
	 * "alliance": player uses all armies to attack continent;
	 * "standard": player keeps only better defense
	 */
	private double[] FindPathsToContinent(Player player, Continent continent, String type, List<Country> from, List<Country> to, List<Double> maxarmiesleft)
	{   int n=game.getCountries().length+1;
		double defense=0;
		boolean svinajednog=false;
		if(type.equals("alliance"))
			svinajednog=true;
		//Prvih n su tenkovi koji su potrebni za prelazak puta, drugih n su put, a trecih n su pocetne teritorije.
		double[] paths=new double[3*n];
		double[] threats=FindThreats(player);
		List<Country> borders=new ArrayList<>();
		borders.addAll(player.getTerritoriesOwned());
		FindBorders(borders,player,"outer");
		List<Country> territories=TerritoriesOnDistance(continent.getTerritoriesContained(),1, "all");
		for(int i=0;i<borders.size();i++)
		{	Country border=borders.get(i);
			if(territories.contains(border))
			{	borders.remove(border);
				i--;
			}
		}
		for(int i=0;i<n-1;i++)
			if(threats[i+1]>0)
			{	Country country = game.getCountries()[i];
				if(!borders.contains(country))
					continue;
				if(betterdefence.contains(country))
					paths[i+1]=country.getArmies()-3-threats[i+1];
				else if(worsedefence.contains(country)&&!extendedworsedefence.contains(country))
					paths[i+1]=country.getArmies()-3-threats[i+1]*2/3;
				else
					paths[i+1]=country.getArmies()-3;
				paths[2*n+i+1]=i+1;
			}
		borders.addAll(player.getTerritoriesOwned());
		while(!borders.isEmpty())
		{   Country country=borders.get(0);
			List<Country> neighbours=new ArrayList<>();
			neighbours.addAll(country.getNeighbours());
			for(Country neighbour:neighbours)
			{   defense=paths[country.getColor()];
				if(neighbour.getOwner()==player)
					continue;
				if(neighbour.getArmies()==1)
					defense-=1;
				else if(neighbour.getArmies()==2)
					defense-=1.7;
				else
					defense-=(neighbour.getArmies()-1)*1.8+1;
				if(defense>paths[neighbour.getColor()]&&defense>0)
				{   paths[neighbour.getColor()]=defense;
					paths[neighbour.getColor()+n]=country.getColor();
					paths[neighbour.getColor()+2*n]=paths[country.getColor()+2*n];
					if(!borders.contains(neighbour))
						borders.add(neighbour);
				}
			}
			borders.remove(country);
		}
		
		territories.clear();
		territories.addAll(continent.getBorderCountries());
		//za sve teritorije kontinenta trazimo odakle je pronadjen put:
		for(Country country:territories)
		{	Country source = game.getCountryInt((int)paths[2*n+country.getColor()]);
			if(source == null)
				continue;
			if(from.contains(source))
			{	int index = from.indexOf(source);
				if(paths[country.getColor()]>maxarmiesleft.get(index))
				{	maxarmiesleft.remove(index);
					maxarmiesleft.add(index, paths[country.getColor()]);
					if(to!=null)
					{	to.remove(index);
						to.add(country);
					}
				}
			}
			else if(paths[country.getColor()]>10)
			{	from.add(source);
				if(to!=null)
					to.add(country);
				maxarmiesleft.add(paths[country.getColor()]);
			}
		}
		return paths;
	}

	private boolean CheckRepeatedAttack(String result)
	{   Country[] countries=game.getCountries();
		int sum=0;
		for(Country country:countries)
			sum+=country.getArmies();
		if(game.resultsum!=sum)
		{   game.results.clear();
			game.resultsum=sum;
		}
		if(game.results.contains(result))
		{   game.results.clear();
			game.resultsum=0;
			return true;
		}
		else
		{   if(!game.results.contains(result))
				game.results.add(result);
			return false;
		}
	}

	private boolean CheckRepeatedAttack1(String result)
	{   Country[] countries=game.getCountries();
		int sum=0;
		for(Country country:countries)
			sum+=country.getArmies();
		if(game.resultsum!=sum)
		{   game.results.clear();
			game.resultsum=sum;
		}
		if(game.results.contains(result))
			return true;
		else
		{   game.results.add(result);
			return false;
		}
	}

	private void TheMostPowerful(List<int []> sort,int l)
	{   int[] reinforcements=sort.get(0);
		int[] playerindexes=sort.get(1);
			for(int i=0;i<l;i++)
			{   reinforcements[i]=((Player)game.getPlayers().get(i)).getTerritoriesOwned().size()/3;
				reinforcements[i]=Math.max(reinforcements[i],3);
				HashSet<Continent> continents=getContinentsOwned((Player)game.getPlayers().get(i));
				for(Continent continent:continents)
					reinforcements[i]+=continent.getArmyValue();
				playerindexes[i]=i;
			}
			int i,j,k;
			for(i=0;i<l-1;i++)
			{   int max=reinforcements[i],indmax=i;
				for(j=i+1;j<l;j++)
					if(reinforcements[j]>max)
					{   max=reinforcements[j];
						indmax=j;
					}
				if(reinforcements[i]<reinforcements[indmax])
				{   k=reinforcements[i];
					reinforcements[i]=reinforcements[indmax];
					reinforcements[indmax]=k;
					k=playerindexes[i];
					playerindexes[i]=playerindexes[indmax];
					playerindexes[indmax]=k;
				}
			}
	}

	private List<Country> getConnectedEmpire(Country Country)
	{   List<Country> visited=new ArrayList<>();
		Player player=Country.getOwner();
		List<Country> empire=new ArrayList<>();
		empire.add(Country);
		for(int i=0;i<empire.size();i++)
		{   Country country1=empire.get(i);
			visited.remove(country1);
			visited.add(country1);
			HashSet<Country> neighbours=new HashSet<>();
			neighbours.addAll(country1.getNeighbours());
			neighbours.addAll(country1.getIncomingNeighbours());
			//neighbours.retainAll(player.getTerritoriesOwned());
			neighbours=retainAll(player,neighbours);
			neighbours.removeAll(visited);
			empire.addAll(neighbours);
			visited.removeAll(neighbours);
			visited.addAll(neighbours);
		}
		return empire;
	}

	private List<Country> getLargestEmpire(Player player)
	{   List<Country> largestempire=new ArrayList<>();
		List<Country> visited=new ArrayList<>();
		int maxpower=0;
		double maxdistances=0;
		List<Country> countries=new ArrayList<>();
		countries.addAll(player.getTerritoriesOwned());
		while(!countries.isEmpty())
		{   Country country=countries.get(0);
			if(visited.contains(country))
				continue;
			List<Country> empire=new ArrayList<>();
			empire.add(country);
			int power=0;
			double distances=0;
			for(int i=0;i<empire.size();i++)
			{   Country country1=empire.get(i);
				visited.remove(country1);
				visited.add(country1);
				HashSet<Country> neighbours=new HashSet<>();
				neighbours.addAll(country1.getNeighbours());
				neighbours.addAll(country1.getIncomingNeighbours());
				//neighbours.retainAll(player.getTerritoriesOwned());
				neighbours=retainAll(player,neighbours);
				neighbours.removeAll(visited);
				empire.addAll(neighbours);
				visited.removeAll(neighbours);
				visited.addAll(neighbours);
			}
			countries.removeAll(empire);
			for(Country country1:empire)
			{   power+=country1.getArmies();
				distances+=game.sumofdistances[country1.getColor()-1];
			}
			if(empire.size()>largestempire.size())
			{   largestempire=empire;
				maxpower=power;
				maxdistances=distances;
			}
			else if(empire.size()==largestempire.size()&&power>maxpower)
			{   largestempire=empire;
				maxpower=power;
				maxdistances=distances;
			}
			else if(empire.size()==largestempire.size()&&power==maxpower&&distances>maxdistances)
			{   largestempire=empire;
				maxpower=power;
				maxdistances=distances;
			}
		}
		return largestempire;
	}

	/**
	* <=> Countries.removeAll(player.getTeritoriesOwned())
	*/
	public static List<Country> removeAll(Player player,List<Country> Countries)
	{   List<Country> countries=new ArrayList<>();
		for (Country country:Countries)
			if(country.getOwner()!=player)
				countries.add(country);
		return countries;
	}

	public static HashSet<Country> removeAll(Player player,HashSet<Country> Countries)
	{   HashSet<Country> countries=new HashSet<>();
		for (Country country:Countries)
		{   if(country.getOwner()!=player)
				countries.add(country);
		}
		return countries;
	}

	public static List<Country> retainAll(Player player,List<Country> Countries)
	{   List<Country> countries=new ArrayList<>();
		for (Country country:Countries)
			if(country.getOwner()==player)
				countries.add(country);
		return countries;
	}

	public static HashSet<Country> retainAll(Player player,HashSet<Country> Countries)
	{   HashSet<Country> countries=new HashSet<>();
		for (Country country:Countries)
			if(country.getOwner()==player)
				countries.add(country);
		return countries;
	}

	public static List<Country> removeAll(Continent continent,List<Country> Countries)
	{   List<Country> countries=new ArrayList<>();
		for (Country country:Countries)
			if(country.getContinent()!=continent)
				countries.add(country);
		return countries;
	}

	public static HashSet<Country> removeAll(Continent continent,HashSet<Country> Countries)
	{   HashSet<Country> countries=new HashSet<>();
		for (Country country:Countries)
			if(country.getContinent()!=continent)
				countries.add(country);
		return countries;
	}

	public static List<Country> retainAll(Continent continent,List<Country> Countries)
	{   List<Country> countries=new ArrayList<>();
		for (Country country:Countries)
			if(country.getContinent()==continent)
				countries.add(country);
		return countries;
	}

	public static HashSet<Country> retainAll(Continent continent,HashSet<Country> Countries)
	{   HashSet<Country> countries=new HashSet<>();
		for (Country country:Countries)
			if(country.getContinent()==continent)
				countries.add(country);
		return countries;
	}

	public static List<List<Card>> FindBestTrade(RiskGame game, List<Card> cards, int armiesdeficit)
	{   List<Card> result=new ArrayList<>();
		List<List<Card>> results=new ArrayList<>();
		int[] type=new int[3];//cavarly,infantry,cannon
		int wildcard=0/*,cavalry=0,infantry=0,cannon=0*/;
		int max,indmax,armies=0;
		String maxs;
		for(Card card:cards)
		if(card.getName().equals("Cavalry")) type[0]++;
			else if(card.getName().equals("Infantry")) type[1]++;
			else if(card.getName().equals("Cannon")) type[2]++;
			else wildcard++;
		int sumeoftypes=type[0]+type[1]+type[2]+wildcard;
		prvapetlja:
		while(armiesdeficit>=0)
		{   sumeoftypes=type[0]+type[1]+type[2]+wildcard;
			while(type[0]>0&&type[1]>0&&type[2]>0)
			{   result=new ArrayList<>();
				results.add(result);
				for(Card card:cards)
					if(card.getName().equals("Cavalry"))
					{   result.add(card);
						break;
					}
				for(Card card:cards)
					if(card.getName().equals("Infantry"))
					{   result.add(card);
						break;
					}
				for(Card card:cards)
					if(card.getName().equals("Cannon"))
					{   result.add(card);
						break;
					}
				type[0]--;
				type[1]--;
				type[2]--;
				cards.removeAll(result);
				armiesdeficit-=game.getTradeAbsValue("Cavalry","Infantry","Cannon",game.getCardMode());
				armies+=game.getTradeAbsValue("Cavalry","Infantry","Cannon",game.getCardMode());
				if(armiesdeficit<=0)
					break prvapetlja;
			}
			if(type[0]>type[1])
			{   max=type[0];
				indmax=0;
				maxs="Cavalry";
			}
			else
			{   max=type[1];
				indmax=1;
				maxs="Infantry";
			}
			if(type[2]>max)
			{   max=type[2];
				indmax=2;
				maxs="Cannon";
			}
			while(wildcard>0&&type[indmax]>1)
			{   result=new ArrayList<>();
				results.add(result);
				for(Card card:cards)
					if(card.getName().equals("wildcard"))
					{   result.add(card);
						break;
					}
				for(Card card:cards)
					if(card.getName().equals(maxs)&&!result.contains(card))
					{   result.add(card);
						break;
					}
				for(Card card:cards)
					if(card.getName().equals(maxs)&&!result.contains(card))
					{   result.add(card);
						break;
					}
				wildcard--;
				type[indmax]--;
				type[indmax]--;
				cards.removeAll(result);
				armiesdeficit-=game.getTradeAbsValue("wildcard",maxs,maxs,game.getCardMode());
				armies+=game.getTradeAbsValue("wildcard",maxs,maxs,game.getCardMode());
				if(type[0]>type[1])
				{   max=type[0];
					indmax=0;
					maxs="Cavalry";
				}
				else
				{   max=type[1];
					indmax=1;
					maxs="Infantry";
				}
				if(type[2]>max)
				{   max=type[2];
					indmax=2;
					maxs="Cannon";
				}
				if(armiesdeficit<=0)
					break prvapetlja;
			}
			while(type[indmax]>2)
			{   result=new ArrayList<>();
				results.add(result);
				for(Card card:cards)
					if(card.getName().equals(maxs)&&!result.contains(card))
					{   result.add(card);
						break;
					}
				for(Card card:cards)
					if(card.getName().equals(maxs)&&!result.contains(card))
					{   result.add(card);
						break;
					}
				for(Card card:cards)
					if(card.getName().equals(maxs)&&!result.contains(card))
					{   result.add(card);
						break;
					}
				type[indmax]--;
				type[indmax]--;
				type[indmax]--;
				cards.removeAll(result);
				armiesdeficit-=game.getTradeAbsValue(maxs,maxs,maxs,game.getCardMode());
				armies+=game.getTradeAbsValue(maxs,maxs,maxs,game.getCardMode());
				if(type[0]>type[1])
				{   max=type[0];
					indmax=0;
					maxs="Cavalry";
				}
				else
				{   max=type[1];
					indmax=1;
					maxs="Infantry";
				}
				if(type[2]>max)
				{   max=type[2];
					indmax=2;
					maxs="Cannon";
				}
				if(armiesdeficit<=0)
					break prvapetlja;
			}
			if(type[0]+type[1]+type[2]+wildcard<sumeoftypes)
				sumeoftypes=type[0]+type[1]+type[2]+wildcard;
			else
				break;
		}
		return results;
	}

	/**
	 * Contains quick information about the player
	 */
	static class PlayerState implements Comparable<PlayerState> {
		Player p;
		double attackValue;
		int defenseValue;
		int attackOrder;
		double playerValue;
		Set<Continent> owned;
		int armies;
		boolean strategic;

		public int compareTo(PlayerState ps) {
			if (playerValue != ps.playerValue) {
				return (int)Math.signum(playerValue - ps.playerValue);
			}
			return p.getCards().size() - ps.p.getCards().size();
		}

		public String toString() {
			return p.toString();
		}
	}

	/**
	 * Overview of the Game
	 */
	static class GameState {
		PlayerState me;
		Player[] owned;
		List<PlayerState> orderedPlayers;
		List<Player> targetPlayers = new ArrayList<>(3);
		Set<Country> capitals;
		PlayerState commonThreat;
		boolean breakOnlyTargets;
	}

	/**
	 * A single target for attack that may contain may possible attack routes
	 */
	static class AttackTarget implements Comparable<AttackTarget>, Cloneable {
		int remaining = Integer.MIN_VALUE;
		int[] routeRemaining;
		int[] eliminationScore;
		Country[] attackPath;
		Country targetCountry;
		int depth;

		public AttackTarget(int fromCountries, Country targetCountry) {
			routeRemaining = new int[fromCountries];
			Arrays.fill(routeRemaining, Integer.MIN_VALUE);
			attackPath = new Country[fromCountries];
			this.targetCountry = targetCountry;
		}

		public String toString() {
			StringBuffer sb = new StringBuffer();
			sb.append(targetCountry).append(" ").append(remaining).append(":(");
			for (int i = 0; i < attackPath.length; i ++) {
				if (attackPath[i] == null) {
					continue;
				}
				sb.append(attackPath[i]).append(" ").append(routeRemaining[i]).append(" ");
			}
			sb.append(")");
			return sb.toString();
		}

		public int compareTo(AttackTarget obj) {
			int diff = remaining - obj.remaining;
			if (diff != 0) {
				return diff;
			}
			return targetCountry.getColor() - obj.targetCountry.getColor();
		}

		public AttackTarget clone() {
			try {
				return (AttackTarget) super.clone();
			} catch (CloneNotSupportedException e) {
				throw new RuntimeException(e);
			}
		}
	}

	/**
	 * A target to eliminate
	 */
	static class EliminationTarget implements Comparable<EliminationTarget> {
		List<AttackTarget> attackTargets = new ArrayList<AttackTarget>();
		PlayerState ps;
		boolean target;
		boolean allOrNone;
		Continent co;

		public int compareTo(EliminationTarget other) {
			if (this.target) {
				return -1;
			}
			if (other.target) {
				return 1;
			}
			int diff = other.ps.p.getCards().size() - ps.p.getCards().size();
			if (diff != 0) {
				return diff;
			}
			return ps.defenseValue - other.ps.defenseValue;
		}

		public String toString() {
			return "Eliminate " + (co != null?co:ps.p);
		}
	}

	private String simplePlacement() {
		if ( !game.NoEmptyCountries()) {
		    return "autoplace";
		}
		List<Country> t = cplayer.getTerritoriesOwned();
		List<Country> n = findAttackableTerritories(cplayer, false);
		List<Country> copy = new ArrayList<>(n);
		Country c = null;
		if (n.isEmpty() || t.size() == 1) {
			c = t.get(0);
		    return getPlaceCommand(c, cplayer.getExtraArmies());
		}
		if (n.size() == 1) {
			c = n.get(0);
			return getPlaceCommand(c, cplayer.getExtraArmies());
		}
		HashSet<Country> toTake = new HashSet<>();
		Country fallback = null;
		Country overload = null;
		int additional = 1;
		while (!n.isEmpty()) {
			c = n.remove( r.nextInt(n.size()) );
			List<Country> cn = c.getNeighbours();
			for (int i = 0; i < cn.size(); i++) {
				Country other = cn.get(i);
				if (other.getOwner() == cplayer || toTake.contains(other)) {
					continue;
				}
				int diff = 0;
				if (game.getMaxDefendDice() == 2) {
					diff = c.getArmies() - 2 - (3*other.getArmies()/2 + other.getArmies()%2);
				} else {
					diff = c.getArmies() - 2 - 2*other.getArmies();
				}

				if (diff >= 0) {
					if (diff < other.getArmies()*3) {
						//we have enough, but try to overload to be safe
						overload = c;
						additional = other.getArmies()*3 - diff;
					}
					toTake.add(other);
					continue;
				}
				if (-diff <= cplayer.getExtraArmies()) {
					return getPlaceCommand(c, -diff);
				}
				if (fallback == null) {
					fallback = c;
					additional = Math.max(1, -diff);
				}
			}
		}
		if (fallback == null) {
			if (overload != null) {
				return getPlaceCommand(overload, additional);
			}
			//we're fully overloaded, just place the rest
			return getPlaceCommand(randomCountry(copy), cplayer.getExtraArmies());
		}
		return getPlaceCommand(fallback, additional);
	}

    /**
     * ai looks at all the continents and tries to see which one it should place on
     * first it simply looks at the troops on each continent
     * then it looks at each player's potential moves.
	 */
	private String findEmptyCountry() {
		Continent[] cont = game.getContinents();

		double check = -Double.MAX_VALUE;
		Country toPlace = null;
		Map<Player, Integer> players = new HashMap<Player, Integer>();
		for (int i = 0; i < this.game.getPlayers().size(); i++) {
			players.put((Player) this.game.getPlayers().get(i), Integer.valueOf(i));
		}

		List<Continent> conts = new ArrayList<Continent>(Arrays.asList(cont));
		Collections.sort(conts, new Comparator<Continent>() {

			@Override
			public int compare(Continent arg0, Continent arg1) {
				return (int)Math.signum(getContinentValue(arg1) - getContinentValue(arg0));
			}
		});

		outer: for (int i = 0; i < conts.size(); i++) {
			Continent co = conts.get(i);

			List<Country> ct = co.getTerritoriesContained();
			int bestCountryScore = 0;

			boolean hasFree = false;
			Country preferedCountry = null;
			int[] troops = new int[game.getPlayers().size()];

			boolean hasPlacement = false;
			Player otherOwner = null;
			for (int j = 0; j < ct.size(); j++) {
				Country country = ct.get(j);
				if (country.getOwner() == null) {
					hasFree = true;
					int countryScore = scoreCountry(country);
					if (preferedCountry == null || countryScore < bestCountryScore || (countryScore == bestCountryScore && r.nextBoolean())) {
						bestCountryScore = countryScore;
						preferedCountry = country;
					}
				} else {
					Integer index = players.get(country.getOwner());
					troops[index.intValue()]++;
					if (country.getOwner() == cplayer) {
						hasPlacement = true;
					} else if (otherOwner == null) {
						otherOwner = country.getOwner();
					} else if (otherOwner != country.getOwner() && r.nextBoolean()) {
						hasPlacement = true; //this is contested
					}
				}
			}

			if (!hasFree) {
				continue;
			}

			if (type == PLAYER_AI_HARD && !hasPlacement) {
				return getPlaceCommand(preferedCountry, 1);
			}

			/* Calculate the base value of that continent */
			double continentValue = getContinentValue(co);

			for (int j = 0; j < troops.length; j++) {
				int numberofEnemyUnits = 0;
				int territorynum = 1;
				int numberOfEnemies = 0;
				for (int k = 0; k < troops.length; k++) {
					if (j == k) {
						territorynum += troops[k];
					} else {
						numberofEnemyUnits += troops[k];
						if (troops[k] > 0) {
							numberOfEnemies++;
						}
					}
				}

				double score = territorynum / Math.max(1d, (numberofEnemyUnits * numberOfEnemies));
				score *= continentValue;
				score /= bestCountryScore;

				Player p = (Player)game.getPlayers().get(j);

				if (p != this.cplayer) {
					//always block
					if (territorynum == ct.size()) {
						toPlace = preferedCountry;
						break outer;
					}
				}

				if (check <= score) {
					check = score;
					toPlace = preferedCountry;
				} else if (toPlace == null) {
					toPlace = preferedCountry;
				}
			}
		}

		if (toPlace == null) {
			return "autoplace";
		}
		return getPlaceCommand(toPlace, 1);
	}

	/**
	 * Gives a score (lower is better) to a country
	 */
	protected int scoreCountry(Country country) {
		final int n = country.getIncomingNeighbours().size();
		int countryScore = n + 6; //normalize so that 1 is the best score for an empty country
		if (country.getArmies() > 0) {
			countryScore += n;
			countryScore -= country.getArmies();
		}
		if (n < 3) {
			countryScore -= 2;
		}
		if (game.getSetupDone() && country.getCrossContinentNeighbours().size() == 1) {
			countryScore -= 3;
		}
		int neighborBonus = 0;
		int neighbors = 0;
		//defense
		for (int k = 0; k < n; k++) {
			Country cn = country.getIncomingNeighbours().get(k);
			if (cn.getOwner() == cplayer) {
				neighborBonus-=cn.getArmies();
				neighbors++;
			} else if (cn.getOwner() != null) {
				countryScore+=(cn.getArmies()/2 + cn.getArmies()%2);
			}
		}
		int n1 = country.getNeighbours().size();
		//attack
		for (int k = 0; k < n1; k++) {
			Country cn = (Country) country.getNeighbours().get(k);
			if (cn.getOwner() == cplayer) {
				neighborBonus-=cn.getArmies();
				neighbors++;
			} else if (cn.getOwner() == null && cn.getContinent() != country.getContinent()) {
				countryScore--;
			}
		}

		neighbors = neighbors/2 + neighbors%2;
		countryScore += neighborBonus/4 + neighborBonus%2;

		if (!game.getSetupDone() || neighbors > 1) {
			countryScore -= Math.pow(neighbors, 2);
			if (!game.getSetupDone()) {
				countryScore = Math.max(1, countryScore);
			}
		}
		return countryScore;
	}

	/**
	 * General planning method for both attack and placement
	 * TODO should save placement planning state over the whole planning phase (requires refactoring of the aiplayer)
	 *      and should consider all placement moves waited by a utility/probability function and possibly combined
	 *      using an approximation algorithm - currently the logic is greedy and will miss easy lower priority opportunities
	 * @param attack
	 * @return
	 */
	private String plan(boolean attack) {
		List<Country> attackable = findAttackableTerritories(cplayer, attack);
		if (attack && attackable.isEmpty()) {
			return "endattack";
		}
		GameState gameState = getGameState(cplayer, false);

		//kill switch
		if (attack && (game.getCurrentPlayer().getStatistics().size() > MAX_AI_TURNS && (gameState.me.playerValue < gameState.orderedPlayers.get(gameState.orderedPlayers.size() - 1).playerValue || r.nextBoolean()))) {
			boolean keepPlaying = false;
			for (int i = 0; i < game.getPlayers().size(); i++) {
				Player p = (Player)game.getPlayers().get(i);
				if (p.getType() == Player.PLAYER_HUMAN && !p.getTerritoriesOwned().isEmpty()) {
					keepPlaying = true;
					break;
				}
			}
			if (!keepPlaying) {
				Country attackFrom = attackable.get(r.nextInt(attackable.size()));
				for (Country c : (List<Country>)attackFrom.getNeighbours()) {
					if (c.getOwner() != cplayer) {
						return "attack " + attackFrom.getColor() + " " + c.getColor();
					}
				}
			}
		}

		HashMap<Country, AttackTarget> targets = searchAllTargets(attack, attackable, gameState);

		//easy seems to be too hard based upon player feedback, so this dumbs down the play with a greedy attack
		if (attack && cplayer.getType() == PLAYER_AI_EASY && game.getMaxDefendDice() == 2 && game.isCapturedCountry() && r.nextBoolean()) {
			ArrayList<AttackTarget> targetList = new ArrayList<AIDomination.AttackTarget>(targets.values());
			Collections.sort(targetList, Collections.reverseOrder());
			for (AttackTarget at : targetList) {
				if (at.remaining < 1) {
					break;
				}
				int route = findBestRoute(attackable, gameState, attack, null, at, gameState.targetPlayers.get(0), targets);
				Country start = attackable.get(route);
				return getAttack(targets, at, route, start);
			}
		}

		return plan(attack, attackable, gameState, targets);
	}

	private HashMap<Country, AttackTarget> searchAllTargets(Boolean attack, List<Country> attackable, GameState gameState) {
		HashMap<Country, AttackTarget> targets = new HashMap<Country, AttackTarget>();
		for (int i = 0; i < attackable.size(); i++) {
			Country c = attackable.get(i);
			int attackForce = c.getArmies();
			searchTargets(targets, c, attackForce, i, attackable.size(), game.getSetupDone()?cplayer.getExtraArmies():(cplayer.getExtraArmies()/2+cplayer.getExtraArmies()%2), attack, gameState);
		}
		return targets;
	}

	protected String plan(boolean attack, List<Country> attackable, GameState gameState,
			Map<Country, AttackTarget> targets) {
		boolean shouldEndAttack = false;
		boolean pressAttack = false;
		int extra = cplayer.getExtraArmies();
		Set<Country> allCountriesTaken = new HashSet<>();
		List<EliminationTarget> continents = findTargetContinents(gameState, targets, attack, true);
		List<Country> v = getBorder(gameState);
		boolean isTooWeak = false;

		//special case planning
		if (game.getSetupDone()) {
			pressAttack = pressAttack(gameState);
			shouldEndAttack = shouldEndAttack(gameState);
			isTooWeak = isTooWeak(gameState);
			//eliminate
			List<EliminationTarget> toEliminate = findEliminationTargets(targets, gameState, attack, extra);
			if (!toEliminate.isEmpty()) {
				Collections.sort(toEliminate);
				for (int i = 0; i < toEliminate.size(); i++) {
					EliminationTarget et = toEliminate.get(i);
					//don't pursue eliminations that will weaken us too much
					int totalCards = cplayer.getCards().size() + et.ps.p.getCards().size();
					if (type == PLAYER_AI_HARD
							&& gameState.orderedPlayers.size() > 1
							&& gameState.me.playerValue < gameState.orderedPlayers.get(0).playerValue
							&& shouldEndAttack
							&& et.ps.armies > gameState.me.armies*.4
						    && et.ps.armies - getCardEstimate(et.ps.p.getCards().size()) > (totalCards>RiskGame.DEFAULT_MAX_CARDS?1:(gameState.me.playerValue/gameState.orderedPlayers.get(0).playerValue)) * getCardEstimate(cplayer.getCards().size() + et.ps.p.getCards().size())) {
						toEliminate.remove(i--);
						continue;
					}
					if ((et.ps.p.getCards().isEmpty() && gameState.orderedPlayers.get(0).playerValue > .7*gameState.me.playerValue)
							|| (et.ps.p.getCards().size() > 2 && cplayer.getCards().size() + et.ps.p.getCards().size() <= RiskGame.DEFAULT_MAX_CARDS)) {
						//don't consider in a second pass
						toEliminate.remove(i--);
					}
					String result = eliminate(attackable, targets, gameState, attack, extra, allCountriesTaken, et, shouldEndAttack, false);
					if (result != null) {
						eliminating = true;
						return result;
					}
				}
			}

			String objective = planObjective(attack, attackable, gameState, targets, allCountriesTaken, pressAttack, shouldEndAttack, true);
			if (objective != null) {
				return objective;
			}

			if (type == PLAYER_AI_HARD && gameState.orderedPlayers.size() > 1
					&& (isIncreasingSet() || gameState.me.playerValue > gameState.orderedPlayers.get(0).playerValue)) {
				//consider low probability eliminations
				if (!toEliminate.isEmpty()) {
					if (!attack) {
						//redo the target search using low probability
						HashMap<Country, AttackTarget> newTargets = searchAllTargets(true, attackable, gameState);
						outer: for (int i = 0; i < toEliminate.size(); i++) {
							EliminationTarget et = toEliminate.get(i);
							//reset the old targets - the new ones contain the new remaining estimates
							for (int j = 0; j < et.attackTargets.size(); j++) {
								AttackTarget newTarget = newTargets.get(et.attackTargets.get(j).targetCountry);
								if (newTarget == null) {
									//TODO: I don't believe this should be happening
									//throw new AssertionError(et.attackTargets.get(j).targetCountry + " no longer reachable");
									continue outer;
								}
								et.attackTargets.set(j, newTarget);
							}
							String result = eliminate(attackable, newTargets, gameState, attack, extra, allCountriesTaken, et, shouldEndAttack, true);
							if (result != null) {
								eliminating = true;
								return result;
							}
						}
					} else if (isIncreasingSet()){
						//try to pursue the weakest player
						EliminationTarget et = toEliminate.get(0);
						et.allOrNone = false;
						String result = eliminate(attackable, targets, gameState, attack, extra, allCountriesTaken, et, shouldEndAttack, true);
						if (result != null) {
							return result;
						}
					}
				}
				//just try to stay in the game
				if (isIncreasingSet() && gameState.me.defenseValue < gameState.orderedPlayers.get(0).attackValue) {
					shouldEndAttack = true;
				}
			}

			if (!attack && allCountriesTaken.isEmpty() && shouldEndAttack && !pressAttack && !game.getCards().isEmpty()) {
				String result = ensureRiskCard(attackable, gameState, targets, pressAttack,
						continents);
				if (result != null) {
					return result;
				}
			}

			//attack the common threat
			if ((gameState.commonThreat != null && !gameState.commonThreat.owned.isEmpty()) || (gameState.breakOnlyTargets && !isTooWeak)) {
				String result = breakContinent(attackable, targets, gameState, attack, pressAttack, v);
				if (result != null) {
					return result;
				}
			}

			if (!attack && (gameState.orderedPlayers.size() > 1 || cplayer.getCapital() != null || cplayer.getMission() != null || game.getMaxDefendDice() > 2)) {
				String result = fortify(gameState, attackable, true, v);
				if (result != null) {
					//prefer attack to fortification
					if (!continents.isEmpty() && pressAttack && cplayer.getCapital() == null) {
						String toAttack = eliminate(attackable, targets, gameState, attack, extra, allCountriesTaken, continents.get(0), false, false);
						if (toAttack != null) {
							return toAttack;
						}
					}
					return result;
				}
			}

			//free a continent, but only plan to do so if in a good position
			//TODO: this does not consider countries already committed
			if (pressAttack || (type != PLAYER_AI_HARD && attack) || (type == PLAYER_AI_HARD && !isTooWeak
					&& (cplayer.getMission() != null || !gameState.me.owned.isEmpty() || continents.isEmpty() || attack))) {
				String result = breakContinent(attackable, targets, gameState, attack, pressAttack, v);
				if (result != null) {
					return result;
				}
			}
		} else if (!attack) {
			String result = fortify(gameState, attackable, game.getMaxDefendDice() == 2, v);
			if (result != null) {
				return result;
			}
		}

		String objective = planObjective(attack, attackable, gameState, targets, allCountriesTaken, pressAttack, shouldEndAttack, false);
		if (objective != null) {
			return objective;
		}

		//take over a continent
		if (!continents.isEmpty() && (!shouldEndAttack
				|| (!game.isCapturedCountry() && !game.getCards().isEmpty())
				|| !attack
				|| gameState.commonThreat != null
				|| (!isTooWeak && (gameState.breakOnlyTargets || gameState.me.defenseValue > gameState.orderedPlayers.get(0).attackValue)))) {
			int toConsider = continents.size();
			if (attack && isTooWeak) {
				toConsider = 1;
			}
			for (int i = 0; i < toConsider; i++) {
				String result = eliminate(attackable, targets, gameState, attack, extra, allCountriesTaken, continents.get(i), shouldEndAttack, false);
				if (result != null) {
					eliminating = true;
					for (Country c : (List<Country>)continents.get(i).co.getTerritoriesContained()) {
						if (c.getOwner() != cplayer && !allCountriesTaken.contains(c)) {
							eliminating = false;
							break;
						}
					}
					if (shouldProactivelyFortify(continents.get(i).co,
							attack, attackable, gameState,
							targets, pressAttack, continents)) {
						//fortify proactively
						List<Country> border = new ArrayList<>();
						for (Country c : (List<Country>)continents.get(i).co.getBorderCountries()) {
							if (c.getOwner() == cplayer) {
								border.add(c);
							}
						}
						String placement = fortify(gameState, attackable, false, border);
						if (placement != null) {
							return placement;
						}
					}
					return result;
				}
			}
			if (!attack) {
				AttackTarget min = null;
				for (int i = 0; i < toConsider; i++) {
					EliminationTarget et = continents.get(i);
					for (int k = 0; k < et.attackTargets.size(); k++) {
						AttackTarget at = et.attackTargets.get(k);
						if (min == null || (!allCountriesTaken.contains(at.targetCountry) && at.remaining < min.remaining)) {
							min = at;
						}
					}
				}
				if (min != null) {
					int route = findBestRoute(attackable, gameState, attack, min.targetCountry.getContinent(), min, game.getSetupDone()?(Player)gameState.targetPlayers.get(0):null, targets);
					if (route != -1) {
						int toPlace = -min.routeRemaining[route] + 2;
						if (toPlace < 0) {
							toPlace = cplayer.getExtraArmies()/3;
						}
						return getPlaceCommand(attackable.get(route), toPlace);
					}
				}
			}
		}

		if (attack) {
			return lastAttacks(attack, attackable, gameState, targets, shouldEndAttack, v);
		}

		String result = fortify(gameState, attackable, false, v);
		if (result != null) {
			return result;
		}

		//fail-safe - TODO: should probably just pile onto the max
		return super.getPlaceArmies();
	}

	protected String planObjective(boolean attack, List<Country> attackable,
			GameState gameState, Map<Country, AttackTarget> targets,
			Set<Country> allCountriesTaken, boolean pressAttack, boolean shouldEndAttack, boolean highProbability) {
		return null;
	}

	protected boolean shouldProactivelyFortify(Continent c, boolean attack,
			List<Country> attackable, GameState gameState,
			Map<Country, AttackTarget> targets, boolean pressAttack,
			List<EliminationTarget> continents) {
		return type == PLAYER_AI_HARD && !isIncreasingSet() && eliminating
				&& gameState.commonThreat == null && !attack && ensureRiskCard(attackable, gameState, targets, pressAttack, continents)==null;
	}

	protected boolean isIncreasingSet() {
		return game.getCardMode() == RiskGame.CARD_INCREASING_SET && (type != PLAYER_AI_HARD || game.getNewCardState() > 12) && (!game.getCards().isEmpty() || game.isRecycleCards());
	}

	private String ensureRiskCard(List<Country> attackable, GameState gameState,
			Map<Country, AttackTarget> targets, boolean pressAttack, List<EliminationTarget> continents) {
		if (this.type == AIDomination.PLAYER_AI_EASY) {
			return null;
		}
		List<AttackTarget> attacks = new ArrayList<AttackTarget>(targets.values());
		Collections.sort(attacks);
		AttackTarget target = null;
		boolean found = false;
		int bestRoute = 0;
		for (int i = attacks.size() - 1; i >= 0; i--) {
			AttackTarget at = attacks.get(i);
			if (target != null && at.remaining < target.remaining) {
				break;
			}
			if (found) {
				continue;
			}
			if (at.remaining > 0) {
				target = null;
				break;
			}
			if (continents.size() > 0 && at.targetCountry.getContinent() == continents.get(0).co) {
				bestRoute = findBestRoute(attackable, gameState, pressAttack, null, at, game.getSetupDone()?(Player) gameState.targetPlayers.get(0):null, targets);
				target = at;
				found = true;
			} else {
				int route = findBestRoute(attackable, gameState, pressAttack, null, at, game.getSetupDone()?(Player) gameState.targetPlayers.get(0):null, targets);
				if (target == null || gameState.targetPlayers.contains(at.targetCountry.getOwner()) || r.nextBoolean()) {
					bestRoute = route;
					target = at;
				}
			}
		}
		if (target != null) {
			return getPlaceCommand(attackable.get(bestRoute), -target.remaining + 1);
		}
		return null;
	}

	/**
	 * one last pass looking to get a risk card or reduce forces
	 */
	private String lastAttacks(boolean attack, List<Country> attackable,
		GameState gameState, Map<Country, AttackTarget> targets, boolean shouldEndAttack, List<Country> border) {
		boolean isTooWeak = isTooWeak(gameState) && gameState.me.defenseValue < .5*gameState.orderedPlayers.get(0).defenseValue;
		boolean forceReduction = game.isCapturedCountry() || game.getCards().isEmpty() || gameState.me.playerValue > 1.5*gameState.orderedPlayers.get(0).playerValue;
		List<AttackTarget> sorted = new ArrayList<AttackTarget>(targets.values());
		Collections.sort(sorted);
		for (int i = sorted.size() - 1; i >= 0; i--) {
			AttackTarget target = sorted.get(i);
			if (target.depth > 1) {
				break; //we don't want to bother considering anything beyond an initial attack
			}
			int bestRoute = findBestRoute(attackable, gameState, attack, null, target, gameState.targetPlayers.get(0), targets);
			if (bestRoute == -1) {
				continue; //shouldn't happen
			}
			Country attackFrom = attackable.get(bestRoute);
			Country initialAttack = getCountryToAttack(targets, target, bestRoute, attackFrom);
			if (forceReduction) {
				//peephole break continent
				if ((attackFrom.getCrossContinentNeighbours().size() == 1 || !border.contains(attackFrom))
						&& attackFrom.getCrossContinentNeighbours().contains(initialAttack)
						&& ((gameState.commonThreat != null && gameState.commonThreat.p == initialAttack.getOwner()) || gameState.targetPlayers.contains(initialAttack.getOwner()) || (gameState.commonThreat == null && !gameState.breakOnlyTargets))
						&& initialAttack.getContinent().getOwner() != null
						&& (!border.contains(attackFrom) || initialAttack.getArmies() == 1 || attackFrom.getArmies() > 3)
						&& target.remaining >= -(attackFrom.getArmies()/2 + attackFrom.getArmies()%2)) {
					return getAttack(targets, target, bestRoute, attackFrom);
				}
				if (gameState.commonThreat != null && gameState.commonThreat.p == initialAttack.getContinent().getOwner() && target.remaining >= -(attackFrom.getArmies()/2 + attackFrom.getArmies()%2)) {
					return getAttack(targets, target, bestRoute, attackFrom);
				}
			} else if (target.remaining >= -(attackFrom.getArmies()/2 + attackFrom.getArmies()%2)) {
				if (gameState.commonThreat != null && !isIncreasingSet() && gameState.commonThreat.p != initialAttack.getOwner() && !gameState.targetPlayers.contains(initialAttack.getOwner()) && initialAttack.getContinent().getOwner() != null) {
					//don't break a continent if there is a common threat
					continue;
				}
				if (type != PLAYER_AI_EASY && attackFrom.getArmies() - target.remaining > getCardEstimate(cplayer.getCards().size()<4?4:5) + initialAttack.getArmies()/2) {
					//don't attack ourselves into the ground and let the force reduction logic kick in
					continue;
				}
				if (isTooWeak && target.remaining < 0 && isIncreasingSet() && cplayer.getCards().isEmpty()) {
					continue;
				}
				return getAttack(targets, target, bestRoute, attackFrom);
			}
		}
		if (!isTooWeak && type != PLAYER_AI_EASY) {
			for (int i = 0; i < sorted.size(); i++) {
				AttackTarget target = sorted.get(i);
				if (target.depth > 1) {
					continue; //we don't want to bother considering anything beyond an initial attack
				}
				int bestRoute = findBestRoute(attackable, gameState, attack, null, target, gameState.targetPlayers.get(0), targets);
				if (bestRoute == -1) {
					continue; //shouldn't happen
				}
				Country attackFrom = attackable.get(bestRoute);
				Country initialAttack = getCountryToAttack(targets, target, bestRoute, attackFrom);
				if (border.contains(attackFrom) && initialAttack.getArmies() < 5) {
					//don't weaken the border for little gain
					continue;
				}
				if (attackFrom.getArmies() < 3 || 
						(game.getMaxDefendDice() > 2 && initialAttack.getArmies() > 2 && (gameState.me.playerValue < 1.5*gameState.orderedPlayers.get(0).playerValue  || game.isCapturedCountry())) ||
						(attackFrom.getArmies() < 4 && attackFrom.getArmies() - 1 <= initialAttack.getArmies())) {
					//don't make an attack where the odds are against us
					continue;
				}
				if (gameState.commonThreat != null) {
					if (gameState.commonThreat.p == initialAttack.getOwner()) {
						return getAttack(targets, target, bestRoute, attackFrom);
					}
				} else {
					if (ownsNeighbours(initialAttack) && target.remaining > -(attackFrom.getArmies()/2 + attackFrom.getArmies()%2)) {
						if ((isIncreasingSet() || gameState.me.playerValue < .8*gameState.orderedPlayers.get(0).playerValue) && !isGoodIdea(gameState, targets, bestRoute, target, attackFrom, null, shouldEndAttack)) {
				        	continue;
				        }
						return getAttack(targets, target, bestRoute, attackFrom);
					}
			        List<Country> neighbours = attackFrom.getIncomingNeighbours();
			        int count = 0;
			        for (int j=0; j<neighbours.size(); j++) {
			           if ( neighbours.get(j).getOwner() != cplayer) {
			        	   count++;
			           }
			        }
			        if (shouldEndAttack && (target.routeRemaining[bestRoute] > 0 && count > 1)) {
			        	//this is just a regular attack, so filter it out
			        	continue;
			        }
			        if (gameState.orderedPlayers.get(0).playerValue > gameState.me.playerValue) {
			        	for (int j = 0; j < gameState.orderedPlayers.size(); j++) {
							PlayerState ps = gameState.orderedPlayers.get(j);
							if (ps.p == initialAttack.getOwner() && (!gameState.breakOnlyTargets || gameState.targetPlayers.contains(ps.p)) &&
									(ps.attackOrder == 1 || gameState.orderedPlayers.size() == 1 || ps.defenseValue > gameState.me.defenseValue*1.2 || (!shouldEndAttack&&isGoodIdea(gameState, targets, bestRoute, target, attackFrom, null, shouldEndAttack)))) {
								return getAttack(targets, target, bestRoute, attackFrom);
							}
						}
			        	continue;
			        }
			        if ((isIncreasingSet() || (game.getCardMode() == RiskGame.CARD_ITALIANLIKE_SET && !game.getCards().isEmpty()) || gameState.me.playerValue < .8*gameState.orderedPlayers.get(0).playerValue) && !isGoodIdea(gameState, targets, bestRoute, target, attackFrom, null, shouldEndAttack)) {
			        	//don't push toward elimination
			        	continue;
			        }
		        	return getAttack(targets, target, bestRoute, attackFrom);
				}
			}
		}
		return "endattack";
	}

	/**
	 * Quick check to see if we're significantly weaker than the strongest player
	 */
	protected boolean isTooWeak(GameState gameState) {
		boolean result = (gameState.orderedPlayers.size() > 1 || cplayer.getMission() != null || cplayer.getCapital() != null) && gameState.me.defenseValue < gameState.orderedPlayers.get(0).attackValue / Math.max(2, gameState.orderedPlayers.size() - 1);
		//early in the game the weakness assessment is too generous as a lot can happen in between turns
		if (!result && type == PLAYER_AI_HARD
				&& gameState.orderedPlayers.size() > 2
				&& (gameState.me.defenseValue < 1.2*gameState.orderedPlayers.get(gameState.orderedPlayers.size() - 1).defenseValue
						|| ((gameState.commonThreat != null || cplayer.getStatistics().size() < 4 || cplayer.getCards().size() < 2) && gameState.me.defenseValue < (game.getMaxDefendDice()==2?1.2:1)*gameState.orderedPlayers.get(0).attackValue))
				&& shouldEndAttack(gameState)) {
			return true;
		}
		return result;
	}

	/**
	 * Stops non-priority attacks if there is too much pressure
	 * @param gameState
	 * @return
	 */
	protected boolean shouldEndAttack(GameState gameState) {
		if (gameState.orderedPlayers.size() < 2 || type == PLAYER_AI_EASY) {
			return false;
		}
		int defense = gameState.me.defenseValue;
		double sum = 0;
		for (int i = 0; i < gameState.orderedPlayers.size(); i++) {
			sum += gameState.orderedPlayers.get(i).attackValue;
		}
		if (defense > sum) {
			return false;
		}
		double ratio = defense/sum;
		if (ratio < .5) {
			return true;
		}
		//be slightly probabilistic about this decision
		return r.nextDouble() > (ratio-.5)*2;
	}

	/**
	 * If the ai should be more aggressive
	 * @param gameState
	 * @return
	 */
	protected boolean pressAttack(GameState gameState) {
		if (this.type == AIDomination.PLAYER_AI_EASY) {
			return r.nextBoolean();
		}
		if (gameState.orderedPlayers.size() < 2) {
			return true;
		}
		int defense = gameState.me.defenseValue;
		double sum = 0;
		for (int i = 0; i < gameState.orderedPlayers.size(); i++) {
			sum += gameState.orderedPlayers.get(i).attackValue;
		}
		return defense > sum;
	}

	/**
	 * Find the continents that we're interested in competing for.
	 * This is based upon how much we control the continent and weighted for its value.
	 */
	private List<EliminationTarget> findTargetContinents(GameState gameState, Map<Country, AttackTarget> targets, boolean attack, boolean filterNoAttacks) {
		Continent[] c = game.getContinents();
		int targetContinents = Math.max(1, c.length - gameState.orderedPlayers.size());
		//step 1 examine continents
		List<Double> vals = new ArrayList<>();
		List<EliminationTarget> result = new ArrayList<EliminationTarget>();
		HashSet<Country> seen = new HashSet<>();
		for (int i = 0; i < c.length; i++) {
			Continent co = c[i];
			if (gameState.owned[i] != null && (gameState.owned[i] == cplayer || (gameState.commonThreat != null && gameState.commonThreat.p != gameState.owned[i]))) {
				continue;
			}
			List<Country> ct = co.getTerritoriesContained();
			List<AttackTarget> at = new ArrayList<AttackTarget>();
			int territories = 0;
			int troops = 0;
			int enemyTerritories = 0;
		    int enemyTroops = 0;
		    seen.clear();
		    //look at each country to see who owns it
			for (int j = 0; j < ct.size(); j++) {
				Country country = ct.get(j);
				if (country.getOwner() == cplayer) {
					territories++;
					troops += country.getArmies();
				} else {
					AttackTarget t = targets.get(country);
					if (t != null) {
						at.add(t);
					}
					enemyTerritories++;
					int toAttack = 0;
					if (gameState.commonThreat == null || gameState.commonThreat.p != country.getOwner()) {
						toAttack += country.getArmies();
					} else {
						//this will draw the attack toward continents mostly controlled by the common threat
						toAttack += country.getArmies()/2;
					}
					if (toAttack >= game.getMaxDefendDice() && (t == null || t.remaining <= 0)) {
						if (game.getMaxDefendDice() == 2) {
							toAttack = 3*toAttack/2;
						} else {
							toAttack *= 2;
						}
					}
					enemyTroops += toAttack;
				}
				//account for the immediate neighbours
				if (!country.getCrossContinentNeighbours().isEmpty()) {
					for (int k = 0; k < country.getCrossContinentNeighbours().size(); k++) {
						Country ccn = country.getCrossContinentNeighbours().get(k);
						if (seen.add(ccn)) { //prevent counting the same neighbor multiple times
							if (ccn.getOwner() == cplayer) {
								if (country.getOwner() != cplayer) {
									troops += ccn.getArmies()-1;
								}
							} else if (gameState.commonThreat == null) {
								enemyTroops += ccn.getArmies()*.8;
							}
						}
					}
				}
			}
			if (at.isEmpty() && filterNoAttacks) {
				continue; //nothing to attack this turn
			}
			int needed = enemyTroops + enemyTerritories + territories - troops + (attack?game.getMaxDefendDice()*co.getBorderCountries().size():0);
			if (attack && game.isCapturedCountry() && (needed*.8 > troops)) {
				continue; //should build up, rather than attack
			}
			double ratio = Math.max(1, territories + 2d*troops + cplayer.getExtraArmies()/(game.getSetupDone()?2:3))/(enemyTerritories + 2*enemyTroops);
			int pow = 2;
			if (!game.getSetupDone()) {
				pow = 3;
			}
			if (ratio < .5) {
				if (gameState.commonThreat != null) {
					continue;
				}
				//when we have a low ratio, further discourage using a divisor
				ratio/=Math.pow(Math.max(1, enemyTroops-enemyTerritories), pow);
			} else {
				targetContinents++;
			}
			if (gameState.commonThreat == null) {
				//lessen the affect of the value modifier as you control more continents
				ratio *= Math.pow(getContinentValue(co), 1d/(gameState.me.owned.size() + 1));
			}
			Double key = Double.valueOf(-ratio);
			int index = Collections.binarySearch(vals, key);
			if (index < 0) {
				index = -index-1;
			}
			vals.add(index, key);
			EliminationTarget et = new EliminationTarget();
			et.allOrNone = false;
			et.attackTargets = at;
			et.co = co;
			et.ps = gameState.orderedPlayers.get(0);
			result.add(index, et);
		}
		if (result.size() > targetContinents) {
			result = result.subList(0, targetContinents);
		}
		return result;
	}

	/**
	 * Find the best route (the index in attackable) for the given target selection
	 */
	protected int findBestRoute(List<Country> attackable, GameState gameState,
			boolean attack, Continent targetCo, AttackTarget selection, Player targetPlayer, Map<Country, AttackTarget> targets) {
		int bestRoute = 0;
		Set<Country> bestPath = null;
		for (int i = 1; i < selection.routeRemaining.length; i++) {
			if (selection.routeRemaining[i] == Integer.MIN_VALUE) {
				continue;
			}
			int diff = selection.routeRemaining[bestRoute] - selection.routeRemaining[i];
			Country start = attackable.get(i);

			if (selection.routeRemaining[bestRoute] == Integer.MIN_VALUE) {
				bestRoute = i;
				continue;
			}

			//short sighted check to see if we're cutting off an attack line
			if (attack && selection.routeRemaining[i] >= 0 && diff != 0 && selection.routeRemaining[bestRoute] >= 0) {
				HashSet<Country> path = getPath(selection, targets, i, start);
				if (bestPath == null) {
					bestPath = getPath(selection, targets, bestRoute, attackable.get(bestRoute));
				}
				HashSet<Country> path1 = new HashSet<>(path);
				for (Iterator<Country> iter = path1.iterator(); iter.hasNext();) {
					Country attacked = iter.next();
					if (!bestPath.contains(attacked) || attacked.getArmies() > 4) {
						iter.remove();
					}
				}
				if (diff < 0 && !path1.isEmpty()) {
			    	HashMap<Country, AttackTarget> specificTargets = new HashMap<Country, AttackTarget>();
			    	searchTargets(specificTargets, start, start.getArmies(), 0, 1, cplayer.getExtraArmies(), attack, Collections.EMPTY_SET, path1, gameState);
			    	int forwardMin = getMinRemaining(specificTargets, start.getArmies(), false, gameState);
			    	if (forwardMin > -diff) {
			    		bestRoute = i;
						bestPath = path;
			    	}
				} else if (diff > 0 && path1.isEmpty() && start.getArmies() >= 3) {
					bestRoute = i;
					bestPath = path;
				}
				continue;
			}

			if (diff == 0 && attack) {
				//range planning during attack is probably too greedy, we try to counter that here
				Country start1 = attackable.get(bestRoute);
				int adjustedCost1 = start1.getArmies() - selection.routeRemaining[bestRoute];
				int adjustedCost2 = start.getArmies() - selection.routeRemaining[i];
				if (adjustedCost1 < adjustedCost2) {
					continue;
				}
				if (adjustedCost2 < adjustedCost1) {
					bestRoute = i;
					continue;
				}
			}

			if ((diff < 0 && (!attack || selection.routeRemaining[bestRoute] < 0))
					|| (diff == 0
							&& ((selection.attackPath[i] != null && selection.attackPath[i].getOwner() == targetPlayer)
									|| (targetPlayer == null || selection.attackPath[bestRoute].getOwner() != targetPlayer) && start.getContinent() == targetCo))) {
				bestRoute = i;
			}
		}
		if (selection.routeRemaining[bestRoute] == Integer.MIN_VALUE) {
			return -1;
		}
		return bestRoute;
	}

	/**
	 * Get a set of the path from start (exclusive) to the given target
	 */
	private HashSet<Country> getPath(AttackTarget at, Map<Country, AttackTarget> targets, int i,
			Country start) {
		HashSet<Country> path = new HashSet<>();
		Country toAttack = at.targetCountry;
		path.add(toAttack);
		while (!start.isNeighbours(toAttack)) {
			at = targets.get(at.attackPath[i]);
			toAttack = at.targetCountry;
			path.add(toAttack);
		}
		return path;
	}

	/**
	 * Return the attack string for the given selection
	 */
	protected String getAttack(Map<Country, AttackTarget> targets, AttackTarget selection, int best,
			Country start) {
		Country toAttack = getCountryToAttack(targets, selection, best, start);
		String result="attack " + start.getColor() + " " + toAttack.getColor();
		if(cplayer.getType()==AIDomination.PLAYER_AI_AVERAGE&&game.getCardMode()==RiskGame.CARD_ITALIANLIKE_SET/*&&smallmap==0*/)
		if(CheckRepeatedAttack(result))
			return "endattack";
		return "attack " + start.getColor() + " " + toAttack.getColor();//Samo to treba.
	}

	/**
	 * Gets the initial country to attack given the final selection
	 */
	private Country getCountryToAttack(Map<Country, AttackTarget> targets, AttackTarget selection,
			int best, Country start) {
		Country toAttack = selection.targetCountry;
		while (!start.isNeighbours(toAttack)) {
			selection = targets.get(selection.attackPath[best]);
			toAttack = selection.targetCountry;
		}
		return toAttack;
	}

	/**
	 * Simplistic fortification
	 * TODO: should be based upon pressure/continent value
	 */
	protected String fortify(GameState gs, List<Country> attackable, boolean minimal, List<Country> borders) {
		int min = Math.max(game.getMaxDefendDice(), getMinPlacement());
		//at least put 2, which increases defensive odds
		for (int i = 0; i < borders.size(); i++) {
			Country c = borders.get(i);
			if (c.getArmies() < min) {
				return getPlaceCommand(c, min - c.getArmies());
			}
		}
		if (minimal && (!game.getSetupDone() || (isIncreasingSet() && cplayer.getCards().size() > 1))) {
			return null;
		}
		for (int i = 0; i < borders.size(); i++) {
			Country c = borders.get(i);
			//this is a hotspot, at least match the immediate troop level
			int diff = additionalTroopsNeeded(c, gs);
			if (diff > 0) {
				return getPlaceCommand(c, Math.min(cplayer.getExtraArmies(), diff));
			}
			if (!minimal && -diff < c.getArmies() + 2) {
				return getPlaceCommand(c, Math.min(cplayer.getExtraArmies(), c.getArmies() + 2 + diff));
			}
		}
		return null;
	}

	/**
	 * Simplistic (immediate) guess at the additional troops needed.
	 */
	protected int additionalTroopsNeeded(Country c, GameState gs) {
		int needed = 0;
		boolean minimal = !gs.capitals.contains(c);
		List<Country> v = c.getIncomingNeighbours();
		for (int j = 0; j < v.size(); j++) {
			Country n = v.get(j);
			if (n.getOwner() != cplayer) {
				if (minimal) {
					needed = Math.max(needed, n.getArmies());
				} else {
					needed += (n.getArmies() -1);
				}
			}
		}
		if (!isIncreasingSet() && type != PLAYER_AI_EASY && gs.commonThreat == null && gs.me.playerValue < gs.orderedPlayers.get(0).playerValue) {
			for (Country cont : c.getCrossContinentNeighbours()) {
				if (!gs.me.owned.contains(c.getContinent()) && cont.getArmies() < cont.getContinent().getArmyValue()) {
					if (gs.me.owned.contains(cont.getContinent()) && needed > 0) {
						needed += cont.getContinent().getArmyValue();
					} else {
						needed = Math.max(needed, cont.getContinent().getArmyValue()/2);
					}
					break;
				}
			}
		}
		int diff = needed - c.getArmies();
		return diff;
	}

	protected int getMinPlacement() {
		return 1;
	}

	/**
	 * Get the border of my continents, starting with actual borders then the front
	 */
	protected List<Country> getBorder(GameState gs) {
		List<Country> borders = new ArrayList<>();
		if (gs.me.owned.isEmpty()) {
			//TODO: could look to build a front
			return borders;
		}
		Set<Country> front = new HashSet<>();
		Set<Country> visited = new HashSet<>();
		for (Iterator<Continent> i = gs.me.owned.iterator(); i.hasNext();) {
			Continent myCont = i.next();
			List<Country> v = myCont.getBorderCountries();
			for (int j = 0; j < v.size(); j++) {
				Country border = v.get(j);
				if (!ownsNeighbours(border) || isAttackable(border)) {
					borders.add(border);
				} else {
					if (border.getCrossContinentNeighbours().size() == 1) {
						Country country = border.getCrossContinentNeighbours().get(0);
						if (country.getOwner() != cplayer) {
							borders.add(country);
							continue;
						}
					}
					List<Country> n = border.getCrossContinentNeighbours();
					findFront(gs, front, myCont, visited, n);
				}
			}
		}
		borders.addAll(front); //secure borders first, then the front
		return borders;
	}

	private boolean ownsNeighbours(Country c) {
		return ownsNeighbours(cplayer, c);
	}

	/**
	 * return true if the country can be attacked
	 */
	private boolean isAttackable(Country c) {
		for (Country country : c.getIncomingNeighbours()) {
			if (country.getOwner() != cplayer) {
				return true;
			}
		}
		return false;
	}

	/**
	 * Search for the front of my continent
	 */
	private void findFront(GameState gs, Set<Country> front, Continent myCont,
			Set<Country> visited, List<Country> n) {
		Stack<Country> c = new Stack<Country>();
		c.addAll(n);
		while (!c.isEmpty()) {
			Country b = c.pop();
			if (!visited.add(b)) {
				continue;
			}
			if (b.getOwner() == cplayer && b.getContinent() != myCont) {
				if (gs.me.owned.contains(b.getContinent())) {
					continue;
				}
				if (isAttackable(b)) {
					front.add(b);
				} else {
					c.addAll(b.getNeighbours());
				}
			}
		}
	}

	/**
	 * Estimates a baseline value for a continent
	 * @param co
	 * @return
	 */
	protected double getContinentValue(Continent co) {
		int players = 0;
		for (int i = 0; i < game.getPlayers().size(); i++) {
			if (!((Player)game.getPlayers().get(i)).getTerritoriesOwned().isEmpty()) {
				players++;
			}
		}
		int freeContinents = game.getContinents().length - players;
		double continentValue = co.getArmyValue() + co.getTerritoriesContained().size()/3;
		int neighbors = 0;
		for (int i = 0; i < co.getBorderCountries().size(); i++) {
			//TODO: update for 1-way
			neighbors += ((Country)co.getBorderCountries().get(i)).getCrossContinentNeighbours().size();
		}
		continentValue /= Math.pow(2*neighbors - co.getBorderCountries().size(), 2);
		if (freeContinents > co.getBorderCountries().size()) {
			continentValue *= co.getBorderCountries().size();
		}
		return continentValue;
	}

	/**
	 * Break continents starting with the strongest player
	 */
	private String breakContinent(List<Country> attackable, Map<Country, AttackTarget> targets, GameState gameState, boolean attack, boolean press, List<Country> borders) {
		List<Continent> toBreak = getContinentsToBreak(gameState);
		if (!attack && type == PLAYER_AI_EASY) {
			return null;
		}
		outer: for (int i = 0; i < toBreak.size(); i++) {
			Continent c = toBreak.get(i);
			Player tp = ((Country)c.getTerritoriesContained().get(0)).getOwner();
			PlayerState ps = null;
			for (int j = 0; j < gameState.orderedPlayers.size(); j++) {
				ps = gameState.orderedPlayers.get(j);
				if (ps.p == tp) {
					break;
				}
			}
			//next level check to see if breaking is a good idea
			if ((!press || !attack) && !gameState.targetPlayers.contains(tp)) {
				if (gameState.commonThreat != null || gameState.breakOnlyTargets) {
					continue outer;
				}
				if (ps.attackOrder != 1 && ps.playerValue < gameState.me.playerValue) {
					continue outer;
				}
			}
			//find the best territory to attack
			List<Country> t = c.getTerritoriesContained();
			int best = Integer.MAX_VALUE;
			AttackTarget selection = null;
			int bestRoute = 0;
			for (int j = 0; j < t.size(); j++) {
				Country target = t.get(j);
				AttackTarget attackTarget = targets.get(target);
				if (attackTarget == null
						|| attackTarget.remaining == Integer.MIN_VALUE
						|| (attackTarget.remaining + cplayer.getExtraArmies() < 1
								&& (!game.getCards().isEmpty() || !press))) {
					continue;
				}
				int route = findBestRoute(attackable, gameState, attack, null, attackTarget, gameState.orderedPlayers.get(0).p, targets);
				Country attackFrom = attackable.get(route);
				if (gameState.commonThreat == null && !gameState.breakOnlyTargets && gameState.me.owned.isEmpty() && attackTarget.routeRemaining[route] + cplayer.getExtraArmies() < 1) {
					continue;
				}
				int cost = attackFrom.getArmies() - attackTarget.routeRemaining[route];
				if (borders.contains(attackFrom)) {
					cost += game.getMaxDefendDice();
				}
				if (cost < best || (cost == best && r.nextBoolean())) {
					best = cost;
					bestRoute = route;
					selection = attackTarget;
				}
			}
			if (selection != null) {
				Country attackFrom = attackable.get(bestRoute);
				if (best > (3*c.getArmyValue() + 2*selection.targetCountry.getArmies()) && game.getMaxDefendDice() == 2) {
					//ensure that breaking doesn't do too much collateral damage
					int value = 3*c.getArmyValue();
					int collateral = 0;
					Set<Country> path = getPath(selection, targets, bestRoute, attackFrom);
					for (Iterator<Country> j = path.iterator(); j.hasNext();) {
						Country attacked = j.next();
						value++;
						if (attacked.getOwner() == selection.targetCountry.getOwner() || gameState.targetPlayers.contains(attacked.getOwner())) {
							if (game.getMaxDefendDice() == 2 || attacked.getArmies() < 3) {
								value += 3*attacked.getArmies()/2 + attacked.getArmies()%2;
							} else {
								value += 2*attacked.getArmies();
							}
						} else {
							if (game.getMaxDefendDice() == 2 || attacked.getArmies() < 3) {
								collateral += 3*attacked.getArmies()/2 + attacked.getArmies()%2;
							} else {
								collateral += 2*attacked.getArmies();
							}
						}
					}
					if (value < best && (!attack || r.nextInt(best - value) != 0) && (gameState.commonThreat == null || !gameState.breakOnlyTargets || value/ps.attackOrder < collateral)) {
						continue outer;
					}
				}
				String result = getMove(targets, attack, selection, bestRoute, attackFrom);
				if (result == null) {
					continue outer;
				}
				breaking = c;
				return result;
			}
		}
		return null;
	}

	/**
	 * Get a list of continents to break in priority order
	 */
	protected List<Continent> getContinentsToBreak(GameState gs) {
		List<Continent> result = new ArrayList<Continent>();
		List<Double> vals = new ArrayList<>();
		for (int i = 0; i < gs.owned.length; i++) {
			if (gs.owned[i] != null && gs.owned[i] != cplayer) {
				Continent co = game.getContinents()[i];
				Double val = Double.valueOf(-getContinentValue(co) * game.getContinents()[i].getArmyValue());
				int index = Collections.binarySearch(vals, val);
				if (index < 0) {
					index = -index-1;
				}
				vals.add(index, val);
				result.add(index, co);
			}
		}
		return result;
	}

	/**
	 * Determine if elimination is possible.  Rather than performing a more
	 * advanced combinatorial search, this planning takes simple heuristic passes
	 */
	protected String eliminate(List<Country> attackable, Map<Country, AttackTarget> targets, GameState gameState, boolean attack, int remaining, Set<Country> allCountriesTaken, EliminationTarget et, boolean shouldEndAttack, boolean lowProbability) {
		AttackTarget selection = null;
		int bestRoute = 0;
		if (type == PLAYER_AI_EASY || (type == PLAYER_AI_AVERAGE && !et.allOrNone && r.nextInt(3) != 0) || (!et.allOrNone && !et.target && shouldEndAttack && attack)) {
			//just be greedy, take the best (least costly) attack first
			for (int i = 0; i < et.attackTargets.size(); i++) {
				AttackTarget at = et.attackTargets.get(i);
				if (at.depth != 1 || allCountriesTaken.contains(at.targetCountry)) {
					continue;
				}
				int route = findBestRoute(attackable, gameState, attack, null, at, et.ps.p, targets);
				Country attackFrom = attackable.get(route);
				if (((at.routeRemaining[route] > 0 && (selection == null || at.routeRemaining[route] < selection.routeRemaining[bestRoute] || selection.routeRemaining[bestRoute] < 1))
						|| (at.remaining > 1 && attackFrom.getArmies() > 3 && (selection != null && at.remaining < selection.remaining)))
						&& isGoodIdea(gameState, targets, route, at, attackFrom, et, attack)) {
					selection = at;
					bestRoute = route;
				}
			}
			return getMove(targets, attack, selection, bestRoute, attackable.get(bestRoute));
		}
		//otherwise we use more logic to plan a more complete attack
		//we start with the targets from easiest to hardest and build up the attack paths from there
		Set<Country> countriesTaken = new HashSet<>(allCountriesTaken);
		Set<Country> placements = new HashSet<>();
		int bestCost = Integer.MAX_VALUE;
		Collections.sort(et.attackTargets, Collections.reverseOrder());
		HashSet<Country> toTake = new HashSet<>();
		for (int i = 0; i < et.attackTargets.size(); i++) {
			AttackTarget at = et.attackTargets.get(i);
			if (!allCountriesTaken.contains(at.targetCountry)) {
				toTake.add(at.targetCountry);
			}
		}
		outer: for (int i = 0; i < et.attackTargets.size() && !toTake.isEmpty(); i++) {
			AttackTarget attackTarget = et.attackTargets.get(i);
			if (!toTake.contains(attackTarget.targetCountry)) {
				continue;
			}
			Country attackFrom = null;
			int route = 0;
			boolean clone = true;
			Set<Country> path = null;
			int pathRemaining;
			while (true) {
				route = findBestRoute(attackable, gameState, attack, null, attackTarget, et.ps.p, targets);
				if (route == -1) {
					if (!et.allOrNone) {
						continue outer;
					}
					return null;
				}
				attackFrom = attackable.get(route);
				if (!placements.contains(attackFrom)) {
					pathRemaining = attackTarget.routeRemaining[route];
					if ((pathRemaining + remaining >= 1 //valid single path
							|| (attackTarget.remaining + remaining >= 2 && attackFrom.getArmies() + remaining >= 4)) //valid combination
							&& (et.allOrNone || isGoodIdea(gameState, targets, route, attackTarget, attackFrom, et, attack))) {
						//TODO this is a choice point if there is more than 1 valid path
						path = getPath(attackTarget, targets, route, attackFrom);
						//check to see if this path is good
						if (Collections.disjoint(path, countriesTaken)) {
							//check to see if we can append this path with a nearest neighbor path
							if (pathRemaining + remaining >= 3) {
								HashSet<Country> exclusions = new HashSet<>(countriesTaken);
								exclusions.addAll(path);
								Map<Country, AttackTarget> newTargets = new HashMap<Country, AttackTarget>();
								searchTargets(newTargets, attackTarget.targetCountry, pathRemaining, 0, 1, remaining, lowProbability?true:attack, toTake, exclusions, gameState);
								//find the best fit new path if one exists
								AttackTarget newTarget = null;
								for (Iterator<AttackTarget> j = newTargets.values().iterator(); j.hasNext();) {
									AttackTarget next = j.next();
									if (toTake.contains(next.targetCountry)
											&& next.routeRemaining[0] < pathRemaining
											&& next.routeRemaining[0] + remaining >= 1) {
										pathRemaining = next.routeRemaining[0];
										newTarget = next;
									}
								}
								if (newTarget != null) {
									path.addAll(getPath(newTarget, newTargets, 0, attackTarget.targetCountry));
									attackTarget.routeRemaining[route] = pathRemaining;
								}
							}
							break; //a good path, continue with planning
						}
					} else if (et.allOrNone && et.attackTargets.size() == 1
							&& type == PLAYER_AI_HARD
							&& attackTarget.remaining + remaining > -attackTarget.targetCountry.getArmies()
							&& gameState.me.playerValue < gameState.orderedPlayers.get(0).playerValue) {
						//allow hard players to always pursue a single country elimination
						path = getPath(attackTarget, targets, route, attackFrom);
						break;
					}
				}
				if (clone) {
					//clone the attack target so that the find best route logic can have a path excluded
					attackTarget = attackTarget.clone();
					attackTarget.routeRemaining = ArraysCopyOf(attackTarget.routeRemaining, attackTarget.routeRemaining.length);
					clone = false;
				}
				attackTarget.routeRemaining[route] = Integer.MIN_VALUE;
			}
			//process the path found and update the countries take and what to take
			for (Iterator<Country> j = path.iterator(); j.hasNext();) {
				Country c = j.next();
				countriesTaken.add(c);
				toTake.remove(c);
			}
			if (pathRemaining < 1) {
				remaining += pathRemaining -1;
			}
			int cost = attackFrom.getArmies() - pathRemaining;
			if (selection == null || (attack && cost < bestCost && cost > 0)) {
				selection = attackTarget;
				bestCost = cost;
				bestRoute = route;
			}
			placements.add(attackFrom);
		}
		Country attackFrom = attackable.get(bestRoute);
		String result = getMove(targets, attack, selection, bestRoute, attackFrom);
		if (result != null) {
			allCountriesTaken.addAll(countriesTaken);
		}
		return result;
	}

    /**
     * @see Arrays#copyOf(int[], int)
     */
    public static int[] ArraysCopyOf(int[] original, int newLength) {
        int[] copy = new int[newLength];
        System.arraycopy(original, 0, copy, 0,
                         Math.min(original.length, newLength));
        return copy;
    }

	/**
	 * ensure that we're not doing something stupid like breaking using too many troops for too little reward or pushing a player to elimination
	 */
	protected boolean isGoodIdea(GameState gameState, Map<Country, AttackTarget> targets, int route, AttackTarget attackTarget, Country attackFrom, EliminationTarget et, boolean attack) {
		Country c = getCountryToAttack(targets, attackTarget, route, attackFrom);
		if (gameState.orderedPlayers.size() > 1 && (et == null || et.ps == null || c.getOwner() != et.ps.p) && !gameState.targetPlayers.contains(c.getOwner())) {
			if (gameState.commonThreat != null && c.getOwner() != gameState.commonThreat.p && c.getContinent().getOwner() != null) {
				return false;
			}
			if (cplayer.getMission() == null && game.getCardMode() == RiskGame.CARD_ITALIANLIKE_SET && c.getOwner().getCards().size() < 4) {
				return true;
			}
			if (gameState.commonThreat != null && c.getOwner().getCards().size() <= 2) {
				return true;
			}
			if (cplayer.getMission() != null || ((attack|| isIncreasingSet()) && (c.getOwner().getCards().size() > 1 || (c.getOwner().getCards().size() == 1 && game.getCards().isEmpty())))) {
				for (int i = gameState.orderedPlayers.size() - 1; i >= 0; i--) {
					PlayerState ps = gameState.orderedPlayers.get(i);
					if (ps.playerValue >= gameState.me.playerValue) {
						break;
					}
					if (ps.p == c.getOwner()) {
						if (ps.attackOrder == 1 && c.getOwner().getCards().size() > 3) {
							return true;
						}
						if (type == PLAYER_AI_HARD && isIncreasingSet()
								&& gameState.me.playerValue < gameState.orderedPlayers.get(0).playerValue
								&& game.getNewCardState() > gameState.me.defenseValue) {
							return true; //you're loosing so just do whatever
						}
						PlayerState top = gameState.orderedPlayers.get(0);
						if (ps.defenseValue - 5*c.getArmies()/4 - c.getArmies()%4 - 1 < 2*(top.attackValue - top.armies/3)/3) {
							return false;
						}
						break;
					}
				}
			}
		}
		return true;
	}

	/**
	 * Gets the move (placement or attack) or returns null if it's not a good attack
	 */
	private String getMove(Map<Country, AttackTarget> targets, boolean attack, AttackTarget selection,
			int route, Country attackFrom) {
		if (selection == null) {
			return null;
		}
		if (attack) {
			if (attackFrom.getArmies() < 5 && selection.remaining < 1) {
				Country toAttack = getCountryToAttack(targets, selection, route, attackFrom);
				if (toAttack.getArmies() >= attackFrom.getArmies()) {
					return null;
				}
			}
			return getAttack(targets, selection, route, attackFrom);
		}
		if (selection.remaining < 1 || selection.routeRemaining[route] < 2) {
			return getPlaceCommand(attackFrom, -selection.routeRemaining[route] + 2);
		}
		return null;
	}

	/**
	 * find the possible elimination targets in priority order
	 * will filter out attacks that seem too costly or if the target has no cards
	 */
	private List<EliminationTarget> findEliminationTargets(Map<Country, AttackTarget> targets, GameState gameState,
			boolean attack, int remaining) {
		List<EliminationTarget> toEliminate = new ArrayList<EliminationTarget>();
		players: for (int i = 0; i < gameState.orderedPlayers.size(); i++) {
			PlayerState ps = gameState.orderedPlayers.get(i);
			Player player2 = ps.p;

			if ((player2.getCards().isEmpty() && player2.getTerritoriesOwned().size() > 1) || ps.defenseValue > gameState.me.attackValue + cplayer.getExtraArmies()) {
				continue;
			}

			boolean isTarget = gameState.targetPlayers.size() > 1 && gameState.targetPlayers.get(0) == player2;
			double divisor = 1;
			int cardCount = player2.getCards().size();
			if ((!isIncreasingSet() || game.getNewCardState() < gameState.me.defenseValue/8) && (!attack || player2.getTerritoriesOwned().size() > 1) && !game.getCards().isEmpty() && cardCount < 3 && (cardCount+cplayer.getCards().size() < game.getMaxCardsPerPlayer())) {
				divisor+=(.5*Math.max(0, isIncreasingSet()?2:4 - cardCount));
			}

			if (!isTarget && ps.defenseValue > gameState.me.armies/divisor + cplayer.getExtraArmies()) {
				continue;
			}

			List<Country> targetCountries = player2.getTerritoriesOwned();
			EliminationTarget et = new EliminationTarget();
			et.ps = ps;
			//check for sufficient troops on critical path
			for (int j = 0; j < targetCountries.size(); j++) {
				Country target = targetCountries.get(j);
				AttackTarget attackTarget = targets.get(target);
				if (attackTarget == null
						|| attackTarget.remaining == Integer.MIN_VALUE
						|| (!attack && -attackTarget.remaining > remaining)) {
					continue players;
				}
				et.attackTargets.add(attackTarget);
			}
			et.target = isTarget;
			et.allOrNone = true;
			toEliminate.add(et);
		}
		return toEliminate;
	}

	private void searchTargets(Map<Country, AttackTarget> targets, Country startCountry, int startArmies, final int start, int totalStartingPoints, int extra, boolean attack, GameState gs) {
		searchTargets(targets, startCountry, startArmies, start, totalStartingPoints, extra, attack, Collections.EMPTY_SET, Collections.EMPTY_SET, gs);
	}

	/**
	 * search using Dijkstra's algorithm
	 * If the way points are set, then we're basically doing a traveling salesman nearest neighbor heuristic.
	 * the attack parameter controls cost calculations
	 *  - true neutral
	 *  - false slightly pessimistic
	 */
	private void searchTargets(Map<Country, AttackTarget> targets, Country startCountry, int startArmies, final int start, int totalStartingPoints, int extra, boolean attack, final Set<Country> wayPoints, final Set<Country> exclusions, GameState gameState) {
		PriorityQueue<AttackTarget> remaining = new PriorityQueue<AttackTarget>(11, new Comparator<AttackTarget>() {
			@Override
			public int compare(AttackTarget o1, AttackTarget o2) {
				int diff = o2.routeRemaining[start] - o1.routeRemaining[start];

				if (type == PLAYER_AI_HARD) {
					//heuristic improvement for hard players.
					//give preference to waypoints based upon presumed navigation order
					if (wayPoints.contains(o1.targetCountry)) {
						if (wayPoints.contains(o2.targetCountry)) {
							int outs1 = neighboursOpen(o1.targetCountry);
							int outs2 = neighboursOpen(o2.targetCountry);
							if (outs1 == 1) {
								if (outs2 == 1) {
									//TODO: handle terminal navigation better
									return -diff; //hardest first
								}
								return 1;
							} else if (outs2 == 1) {
								return -1;
							}
							return diff + 2*(outs1 - outs2);
						}
						return -1;
					}
					if (wayPoints.contains(o2)) {
						return 1;
					}
				}
				return diff;
			}

		    public int neighboursOpen( Country c) {
		        List<Country> neighbours = c.getNeighbours();
		        int count = 0;
		        for (int i=0; i<neighbours.size(); i++) {
		           if ( neighbours.get(i).getOwner() != cplayer && !exclusions.contains(c)) {
		        	   count++;
		           }
		        }
		        return count;
		    }
		});
		if (type == PLAYER_AI_HARD) {
			double ratio = gameState.me.playerValue / gameState.orderedPlayers.get(0).playerValue;
			if (ratio < .4) {
				attack = false; //we're loosing, so be more conservative
			}
		} else if (type == PLAYER_AI_EASY) {
			attack = false; //over estimate
		}
		AttackTarget at = new AttackTarget(totalStartingPoints, startCountry);
		at.routeRemaining[start] = startArmies;
		remaining.add(at);
		outer: while (!remaining.isEmpty()) {
			AttackTarget current = remaining.poll();

			//if this is the nearest waypoint, continue the search from this point
			if (wayPoints.contains(current)) {
				Set<Country> path = getPath(current, targets, start, startCountry);
				exclusions.addAll(path);
				startCountry = current.targetCountry;
				targets.keySet().retainAll(exclusions);
				remaining.clear();
				remaining.add(current);
				continue outer;
			}

			int attackForce = current.routeRemaining[start];
			attackForce -= getMinPlacement();
			attackForce -= Math.min(current.targetCountry.getArmies()/(attack?3:2), current.depth);

			if (attackForce + extra < 1) {
				break;
			}

			List<Country> v = current.targetCountry.getNeighbours();

			for (int i = 0; i < v.size(); i++) {
				Country c = v.get(i);
				if (c.getOwner() == cplayer) {
					continue;
				}
				AttackTarget cumulativeForces = targets.get(c);
				if (cumulativeForces == null) {
					if (exclusions.contains(c)) {
						continue;
					}
					cumulativeForces = new AttackTarget(totalStartingPoints, c);
					targets.put(c, cumulativeForces);
				} else if (cumulativeForces.routeRemaining[start] != Integer.MIN_VALUE) {
					continue;
				}
				cumulativeForces.depth = current.depth+1;
				int available = attackForce;
				int toAttack = c.getArmies();
				if (game.getMaxDefendDice() == 2 || gameState.me.playerValue>gameState.orderedPlayers.get(0).playerValue || gameState.me.p.getType() == PLAYER_AI_EASY) {
					if (attack) {
						while (toAttack >= 10 || (available >= 10 && toAttack >= 5)) {
							toAttack -= 4;
							available -= 3;
						}
					}
					while (toAttack >= 5 || (available >= 5 && toAttack >= 2)) {
						toAttack -= 2;
						available -= 2;
					}

				} else {
					//assume 3
					if (attack) {
					    int rounds = (toAttack - 3)/3;
					    if (rounds > 0) {
					       toAttack -= 3*rounds;
					       available -= 3*rounds;
					    }
					}
				}
				if (attack && available == toAttack + 1 && toAttack <= 2) {
					available = 1; //special case to allow 4 on 2 and 3 on 1 attacks
				} else {
					if (game.getMaxDefendDice() == 2 || toAttack <= 2) {
						available = available - 3*toAttack/2 - toAttack%2;
					} else {
						available = available - 2*toAttack;
					}
				}
				cumulativeForces.attackPath[start] = current.targetCountry;
				cumulativeForces.routeRemaining[start] = available;
				if (cumulativeForces.remaining>=0 && available>=0) {
					cumulativeForces.remaining = cumulativeForces.remaining += available;
				} else {
					cumulativeForces.remaining = Math.max(cumulativeForces.remaining, available);
				}
				remaining.add(cumulativeForces);
			}
		}
	}

    public String getBattleWon() {
    	GameState gameState = getGameState(cplayer, false);
    	return getBattleWon(gameState);
    }

	/**
	 * Get an estimate of the remaining troops after taking all possible targets
	 */
	private int getMinRemaining(HashMap<Country, AttackTarget> targets, int forwardMin, boolean isBorder, GameState gameState) {
		int total = 0;
		for (Iterator<AttackTarget> i = targets.values().iterator(); i.hasNext();) {
			AttackTarget attackTarget = i.next();
			if (attackTarget.remaining < 0 && !isBorder) {
				return 0;
			}
			//estimate a cost for the territory
			total += 1;
			if (game.getMaxDefendDice() == 2 || attackTarget.targetCountry.getArmies() < 3) {
				total += attackTarget.targetCountry.getArmies();
				if (attackTarget.targetCountry.getArmies() < 2) {
					total += attackTarget.targetCountry.getArmies();
				}
			} else {
				total += 2*attackTarget.targetCountry.getArmies();
			}
		}
		if (game.getMaxDefendDice() == 2) {
			forwardMin -= (total *= 1.3);
		} else {
			forwardMin -= total;
		}
		if (type == PLAYER_AI_HARD && !isIncreasingSet() && isBorder && isTooWeak(gameState)) {
			//TODO: let the hard player lookahead further, alternatively just call to plan(true) and mark if we are doing an elimination or something
			return Integer.MAX_VALUE;
		}
		return Math.max(isBorder?game.getMaxDefendDice():0, forwardMin);
	}

    /**
     * Get a quick overview of the game state - capitals, player ordering, if there is a common threat, etc.
     * @param p
     * @param excludeCards
     * @return
     */
    public GameState getGameState(Player p, boolean excludeCards) {
    	List<Player> players = game.getPlayers();
    	GameState g = new GameState();
    	Continent[] c = game.getContinents();
    	if (cplayer.getCapital() == null) {
    		g.capitals = Collections.EMPTY_SET;
    	} else {
    		g.capitals = new HashSet<>();
    	}
    	g.owned = new Player[c.length];
    	for (int i = 0; i < c.length; i++) {
			g.owned[i] = c[i].getOwner();
		}
    	int index = -1;
    	int playerCount = 1;
    	//find the set of capitals
    	for (int i = 0; i < players.size(); i++) {
    		Player player2 = players.get(i);
    		if (player2.getCapital() != null) {
    			g.capitals.add(player2.getCapital());
    		}
    		if (player2.getTerritoriesOwned().isEmpty()) {
    			continue;
    		}
    		if (player2 == p) {
    			index = i;
    		} else {
    			playerCount++;
    		}
    	}
    	g.orderedPlayers = new ArrayList<PlayerState>(playerCount);
    	int attackOrder = 0;
    	int strategicCount = 0;
    	for (int i = 0; i < players.size(); i++) {
    		Player player2 = players.get((index + i)%players.size());
    		if (player2.getTerritoriesOwned().isEmpty()) {
    			continue;
    		}
    		//estimate the trade-in
    		int cards = player2.getCards().size() + 1;
    		int cardEstimate = (i==0&&excludeCards)?0:getCardEstimate(cards);
			PlayerState ps = new PlayerState();
			List<Country> t = player2.getTerritoriesOwned();
			int noArmies = 0;
			int attackable = 0;
			boolean strategic = isStrategic(player2);
			if (strategic) {
				strategicCount++;
			}
			//determine what is available to attack with, discounting if land locked
			for (int j = 0; j < t.size(); j++) {
				Country country = t.get(j);
				noArmies += country.getArmies();
				int available = country.getArmies() - 1;
				if (ownsNeighbours(player2, country)) {
					available = country.getArmies()/2;
				}
				//quick multipliers to prevent turtling/concentration
				if (available > 4) {
					if (available > 8 && strategic) {
						if (available > 13) {
							available *= 1.3;
						}
						available += 2;
					}
					available += 1;
				}
				attackable += available;
			}
			int reenforcements = Math.max(3, player2.getNoTerritoriesOwned()/3) + cardEstimate;
			if (reenforcements > 8 && strategic) {
				reenforcements *= 1.3;
			}
			int attack = attackable + reenforcements;
			HashSet<Continent> owned = new HashSet<>();
			//update the attack and player value for the continents owned
			for (int j = 0; j < g.owned.length; j++) {
				if (g.owned[j] == player2) {
					attack += c[j].getArmyValue();
					if (strategic) {
						ps.playerValue += 3*c[j].getArmyValue();
					} else {
						ps.playerValue += 1.5 * c[j].getArmyValue() + 1;
					}
					owned.add(c[j]);
				}
			}
			ps.strategic = strategic;
			ps.armies = noArmies;
			ps.owned = owned;
			ps.attackValue = attack;
			ps.attackOrder = attackOrder;
			//use a small multiplier for the defensive value
			ps.defenseValue = 5*noArmies/4 + noArmies%4 + player2.getNoTerritoriesOwned();
			ps.p = player2;
			if (i == 0) {
				g.me = ps;
			} else {
				g.orderedPlayers.add(ps);
			}
			ps.playerValue += ps.attackValue + ((game.getMaxDefendDice() == 2 && !isIncreasingSet())?1:game.getMaxDefendDice()>2?3:2)*ps.defenseValue;
			attackOrder++;
    	}
    	//put the players in order of strongest to weakest
    	Collections.sort(g.orderedPlayers, Collections.reverseOrder());
    	//check to see if there is a common threat
    	//the logic will allow the ai to team up against the strongest player
    	//TODO: similar logic could be expanded to understand alliances/treaties
    	if (game.getSetupDone() && !g.orderedPlayers.isEmpty()) {
    		//base top player multiplier
    		double multiplier = game.getCards().isEmpty()?(game.isRecycleCards()?1.2:1.1):(cplayer.getMission()!=null||cplayer.getCapital()!=null)?1.1:1.3;
    		PlayerState topPlayer = g.orderedPlayers.get(0);
    		if (type == AIDomination.PLAYER_AI_EASY) {
				multiplier *= 1.6; //typically this waits too long in the end game
    		} else if (type == AIDomination.PLAYER_AI_HARD && cplayer.getStatistics().size() > 3) {
    			if (!isIncreasingSet()) {
    				//we can be more lenient with more players
    				multiplier = Math.max(1, multiplier - .4 + g.orderedPlayers.size()*.1);
    			} else if (game.getCardMode() != RiskGame.CARD_ITALIANLIKE_SET) {
    				//don't want to pursue the lowest player if there's a good chance someone else will eliminate
    				multiplier *= 1.5;
    			}
    		} else if (type == AIDomination.PLAYER_AI_AVERAGE) {
    			multiplier *= 1.2;
    		}
			g.targetPlayers.add(topPlayer.p);
			//look to see if you and the next highest player are at the multiplier below the highest
    		if (g.orderedPlayers.size() > 1 && topPlayer.playerValue > multiplier * g.me.playerValue) {
    			g.breakOnlyTargets = game.getMaxDefendDice() == 2;
    			PlayerState ps = g.orderedPlayers.get(1);
    			if (topPlayer.playerValue > multiplier * ps.playerValue) {
        			g.commonThreat = topPlayer;
    			} else {
    				//each of the top players is a target
    				g.targetPlayers.add(ps.p);
    			}
    		} else if (type == AIDomination.PLAYER_AI_HARD && isIncreasingSet() && g.orderedPlayers.get(g.orderedPlayers.size()-1).defenseValue/topPlayer.attackValue > .3) {
    			//play for the elimination
    			g.targetPlayers.clear();
    			g.targetPlayers.add(g.orderedPlayers.get(g.orderedPlayers.size()-1).p);
    		}
    	}
    	return g;
    }

	private int getCardEstimate(int cards) {
		int tradeIn = game.getCardMode() != RiskGame.CARD_INCREASING_SET?8:game.getNewCardState();
		int cardEstimate = cards < 3?0:(int)((cards-2)/3.0*tradeIn);
		return cardEstimate;
	}

    /**
     * Provides a quick measure of how the player has performed
     * over the last several turns
     */
	private boolean isStrategic(Player player2) {
		if (player2 == this.cplayer) {
			return false;
		}
		List<Statistic> stats = player2.getStatistics();
		if (stats.size() < 4) {
			return false;
		}
		//look over the last 4 turns
		int end = 4;
		int reenforcements = 0;
		int kills = 0;
		int casualities = 0;
		for (int i = stats.size() - 1; i >= end; i--) {
			Statistic s = stats.get(i);
			reenforcements += s.get(StatType.REINFORCEMENTS);
			kills += s.get(StatType.KILLS);
			casualities += s.get(StatType.CASUALTIES);
			if (s.get(StatType.CONTINENTS) == 0) {
				return false;
			}
		}
		return reenforcements + kills/((player2.getCards().size() > 2)?1:2) > 2*casualities;
	}

    /**
     * Finds all countries that can be attacked from.
     * @param p player object
     * @param attack true if this is durning attack, which requires the territority to have 2 or more armies
     * @return a Vector of countries, never null
     */
    public List<Country> findAttackableTerritories(Player p, boolean attack) {
    	List<Country> countries = p.getTerritoriesOwned();
    	List<Country> result = new ArrayList<>();
    	for (int i=0; i<countries.size(); i++) {
    		Country country = countries.get(i);
    		if ((!attack || country.getArmies() > 1) && !ownsNeighbours(p, country)) {
				result.add(country);
    		}
    	}
    	return result;
    }

    /**
     * Checks whether a country owns its neighbours
     * @param p player object, c Country object
     * @return boolean True if the country owns its neighbours, else returns false
     */
    public boolean ownsNeighbours(Player p, Country c) {
        List<Country> neighbours = c.getNeighbours();

        for (int i=0; i<neighbours.size(); i++) {
           if ( neighbours.get(i).getOwner() != p) {
        	   return false;
           }
        }

        return true;
    }

    @Override
    protected String getTrade(Card[] result) {
    	if (type != PLAYER_AI_EASY) {
    		boolean[] owns = new boolean[result.length];
    		int ownsCount = 0;
    		for (int i = 0; i < result.length; i++) {
    			if (result[i].getCountry() != null && cplayer.getTerritoriesOwned().contains(result[i].getCountry())) {
    				owns[i] = true;
    				ownsCount++;
    			}
    		}
			//swap for a single owned country - TODO: be smarter about which territory to retain
    		if (ownsCount != 1 && cplayer.getCards().size() > 3) {
    			List<Card> toTrade = Arrays.asList(result);
        		for (Card card : (List<Card>)cplayer.getCards()) {
        			if (toTrade.contains(card)) {
        				continue;
        			}
        			if (ownsCount > 1) {
	        			if (card.getCountry() == null || !cplayer.getTerritoriesOwned().contains(card.getCountry())) {
	        				for (int i = 0; i < result.length; i++) {
	        					if (result[i].getName().equals(card.getName())) {
	        						result[i] = card;
	        						if (--ownsCount == 1) {
	        							return super.getTrade(result);
	        						}
	        						break;
	        					}
	        				}
	        			}
        			} else {
        				if (card.getCountry() != null && cplayer.getTerritoriesOwned().contains(card.getCountry())) {
        					for (int i = 0; i < result.length; i++) {
	        					if (result[i].getName().equals(card.getName())) {
	        						result[i] = card;
	        						return super.getTrade(result);
	        					}
	        				}
	        			}
        			}
        		}
    		}
    	}
    	return super.getTrade(result);
    }

}
