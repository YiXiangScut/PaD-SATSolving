package jmetal.myutils.datacollection;


public class CollectionDataForTestMain {

	/**
	 * @param args
	 * @throws Exception 
	 * @throws MatlabConnectionException 
	 * @throws MatlabInvocationException 
	 */
	public static void main(String[] args) throws Exception {

		int runs = 30;
		int t = 2; //Not used
		int nbProduts = 1000;
		long timeMS = 600000;//Not used
		
		String expPath = "./output/";
		
		String [] problems= new String[]{	
				
				/******************* Small-scale*****************  */
				"CounterStrikeSimpleFeatureModel", //24
				"HiPAcc",//31
				"SPLSSimuelESPnP",//32
				"JavaGC",//39
				"Polly", //40
				"DSSample", //41    
				"VP9",//42
				"WebPortal",//43
				"JHipster", //45
				"Drupal", //48
				"SmartHomev2.2",//60
				"VideoPlayer",//71
				"Amazon",//79
				"ModelTransformation", //88
				"CocheEcologico", //94
				"Printers",//172
				"fiasco_17_10",//234
				"uClibc-ng_1_0_29",//269
				"E-shop",//290
				"toybox",//544
				"axTLS", // 684
				"financial",//771 
				"busybox_1_28_0", // 998  			
//	  			/***************Median-scale******************** */
				"mpc50", //1213
				"ref4955",//1218  		
				"linux", //1232
				"csb281", //1233
				"ecos-icse11", //1244
				"ebsa285", //1245
				"vrc4373", // 1247
				"pati", // 1248
				"dreamcast", //1252
				"pc_i82544", //1259
				"XSEngine",  //1260
				"refidt334", //1263
				"ocelot", //1266
				"integrator_arm9", //1267
				"olpcl2294", //1273
				"olpce2294", //1274
				"phycore", // 1274
				"hs7729pci", //1298
				"freebsd-icse11",//1396
				"fiasco",//1638
				"uClinux",//1850
				"Automotive01", //2513 
				"SPLOT-3CNF-FM-5000-1000-0,30-SAT-1",// 5000  			
////	  			 /*******************  Large-scale ***************** */
				 "busybox-1.18.0",//6796
				 "2.6.28.6-icse11", //6888
				 "uClinux-config", //11254
				 "buildroot", // 14910
				 "freetz", //31012	
				};
		
		String [] algorithms = new String[]{			
//				"rSAT4J",
//				"PaD+rSAT4Jnew",
				
		    	"ProbSATRerun",
		    	"PaD+ProbSATRerun",
		};
		
		String [] indicators = new String [] {
	    		"invertedDist",
//	    		"Extension",
//	    		"STD",
	    		"RUNTIME",
//	    		"Fitness",
		};
		
		
		(new CollectionDataForTest(runs, expPath, problems,algorithms,indicators,t,nbProduts,timeMS)).execute();
	}
	
}
