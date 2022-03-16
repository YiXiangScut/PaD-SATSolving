/* GenerateFromExistingResultsMain.java
 * 
 * For different t, we can generate t-wise coverage from sampled results.
 * 
 * Author:  Yi Xiang <xiangyi@scut.edu.cn> or <gzhuxiang_yi@163.com>
 *  
 * Reference: 
 *  
 * Yi Xiang, Han Huang, Miqing Li, Sizhe Li, and Xiaowei Yang, 
 * Looking For Novelty in Search-based Software Product Line Testing, TSE, 2021
 * 
 * Data: 25/01/2021
 * Copyright (c) 2021 Yi Xiang
 * 
 * Note: This is a free software developed based on the open 
 * source projects PLEDGE <https://github.com/christopherhenard/pledge> 
 * and jMetal<http://jmetal.sourceforge.net>. The copy right of PLEDGE 
 * belongs to  its original author, Christopher Henard, and the copy 
 * right of jMetal belongs to Antonio J. Nebro and Juan J. Durillo. 
 * Nevertheless, this current version can be redistributed and/or 
 * modified under the terms of the GNU General Public License
 * as published by the Free Software Foundation, either version 3 of 
 * the License, or (at your option) any later version.
 * 
 * This program is distributed in the hope that it will be useful, 
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU  General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 * 
 */
package spl;

import java.io.File;
import java.util.List;
import java.util.Set;

import spl.fm.Product;
import spl.fm.TSet;
import spl.techniques.SimilarityTechnique;
import spl.utils.FileUtils;


public class GenerateTwiseCoverage {

	public int exisitingT = 2;
	public int nbProds = 100;
	public int t = 6;
	public long timeAllowed; 
	public long evaluations; 
 
	public String outputDir;
	public int runs;
	public String algName;
	private Set<TSet> validTSets;
	 
	public GenerateTwiseCoverage() {
		
	}	

	public void loadTSets(String fmFile) throws Exception {
		 /**
         * 读取T-set
         */        
        String validTsetFile = "./all_FM/"  + fmFile + ".valid" + t + "-Set_" + nbProds + "products";    	    
    
        if (validTsetFile != null && (new File(validTsetFile).exists())) {       	

        	validTSets = SPL_sampler.getInstance().loadValidTSet(validTsetFile);    
//        	System.out.println("Number of validTSets " + validTSets.size());
        	
        }

	}	
	
	public void computeTwiseCoverage(String fmFile) throws Exception{
		 String sNbProds = "" + nbProds;
         String fmFileName = new File(fmFile).getName();
        
         double avgCoverage = 0.0;
                
         String path = outputDir + algName  + "/" + fmFileName + "/Samples/" + sNbProds + "prods/";
                  
         //FileUtils.CheckDir(path); 
         
         String loadProductsPath = outputDir + algName  + "/"  + fmFileName + "/Samples/" + sNbProds + "prods/";            
  	 
         for (int i = 0; i < runs; i++) {
             System.out.println("ComputeTwiseCoverage, run " + (i + 1));
         	
             List<Product> products = null;    
             double sumCoverageValues = 0.0;        
             
             // Load products                            
             products = SPL_sampler.getInstance().loadProductsFromFile(loadProductsPath + "Products." + i);
// 	         shuffle(products); // 洗牌
 	                      
            // Compute coverage
             SPL_sampler.getInstance().computeProductsPartialCoverage(products, SPL_sampler.getInstance().validTSets);                              
           
             for (int j = 0; j < nbProds; j++) {
                 double cov = products.get(j).getCoverage();
                 sumCoverageValues += cov; //累积覆盖率                
             }                  
   
             System.out.println(" t = " + t + " Coverage = " + sumCoverageValues);     
             
             SPL_sampler.getInstance().writeDataToFile(path + t + "wiseCoverage." + i, sumCoverageValues);// write coverage

         } // for runs   
         
	}
	
	public void computeFitness(String fmFile) throws Exception{
		 String sNbProds = "" + nbProds;
        String fmFileName = new File(fmFile).getName();

       
        double avgCoverage = 0.0;
        //double avgFitness = 0.0;
        SimilarityTechnique st = new SimilarityTechnique(SimilarityTechnique.Anti_Dice_Distance, SimilarityTechnique.NEAR_OPTIMAL_SEARCH);
                        
        String path = outputDir + algName  + "/" + fmFileName + "/Samples/" + sNbProds + "prods/"+ timeAllowed + "ms/";
        FileUtils.CheckDir(path); 
        
        String loadProductsPath = outputDir + algName  + "/"  + fmFileName + "/Samples/" + sNbProds + "prods/"+ timeAllowed + "ms/";            
        
        for (int i = 0; i < runs; i++) {
            System.out.println("computeFitness, run " + (i + 1));
        	
            List<Product> products = null; //
            
            // Load products                            
            products = SPL_sampler.getInstance().loadProductsFromFile(loadProductsPath + "Products." + i);
//	         shuffle(products); // 洗牌
	                      
            /*
             * 计算适应度值
             */
//          products = st.prioritize(products);
//          double fitness = st.getLastFitnessComputed();
//            double fitness = st.PD(products);
            double fitness = st.noveltyScoreSum(products, nbProds/2);                                                     

            SPL_sampler.getInstance().writeDataToFile(path + "Fitness." + i, fitness);// write Novelty score        

        } // for runs   
        
	}
	
	public void computeFaultRate(String fmFile) throws Exception{
		String sNbProds = "" + nbProds;
        String fmFileName = new File(fmFile).getName();
                  
        // Write path for faults
        String path =  outputDir + algName  + "/" + fmFileName +"/" + t + "wise/" + sNbProds + "prods/"+ timeAllowed + "ms/";
        FileUtils.CheckDir(path); 
        
        // Load path for products 
        String loadProductsPath = outputDir + algName  + "/" + fmFileName +"/Samples/"  + sNbProds + "prods/"+ timeAllowed + "ms/";
       		 
        // Load path for faults
        String faultsDir = "./all_FM/TSE/" + fmFileName + ".faults/";      
        
        int repeatTimes = 100;        
        
        for (int i = 0; i < runs; i++) {
//          System.out.println("run " + (i + 1));
        	
            List<Product> products = null; 
            // Load products                            
            products = SPL_sampler.getInstance().loadProductsFromFile(loadProductsPath + "Products." + i);
	                  
            double sumFaultsValues = 0.0;               
            double [] faults = new double[repeatTimes];
            
            
            for (int k = 0; k < repeatTimes;k++) {
            	
            	 String faultsFile = faultsDir + "faults." + k;    	
            	 
                 if (faultsFile != null && (new File(faultsFile).exists())) {
                 	           
                 	validTSets = SPL_sampler.getInstance().loadValidTSet(faultsFile);   
//                 	System.out.println("Loading faults. Number of faults " + validTSets.size());
                 	
                 	SPL_sampler.getInstance().computeProductsPartialFaults(products, validTSets);  
                 	
                 	double faultsRate = 0.0;
                    for (int j = 0; j < nbProds; j++) {
                        double coverFaults = products.get(j).getCoverage();
                        faultsRate += coverFaults; //累积错误数       
                    }
                    
                    faults[k] = faultsRate/validTSets.size() * 100;                      
                    sumFaultsValues = sumFaultsValues + faultsRate/validTSets.size() * 100;                    
                 } // IF    
                 
             }  // for k               
                                                     
            sumFaultsValues = sumFaultsValues/repeatTimes;     

            SPL_sampler.getInstance().writeDataToFile(path + "MeanFaultRate." + i, sumFaultsValues);// write mean faults rate  
            SPL_sampler.getInstance().writeDataToFile(path + "FaultArray." + i, faults);// write all fault rates
        } // for runs         
       
	}

  /**
   * Main method
   * @param args
 * @throws Exception 
   */
  public static void main(String[] args) throws Exception {
    GenerateTwiseCoverage gfr = new GenerateTwiseCoverage();
    
    String [] fms = {
    		/** ***************** Small-scale*****************  */
//			"X264",//16
//			"Dune", //17
//			"BerkeleyDBC", //18
//			"lrzip", //20
//			"CounterStrikeSimpleFeatureModel", //24
//			"HiPAcc",//31
//			"SPLSSimuelESPnP",//32
//			"JavaGC",//39
//			"Polly", //40
//			"DSSample", //41    
//			"VP9",//42
//			"WebPortal",//43
//			"7z",// 44
//			"JHipster", //45
//			"Drupal", //48
//			"ElectronicDrum", //52
//			"SmartHomev2.2",//60
//			"VideoPlayer",//71
//			"Amazon",//79
//			"ModelTransformation", //88
//			"CocheEcologico", //94
//			"Printers",//172
//			"fiasco_17_10",//234
//			"uClibc-ng_1_0_29",//269
//			"E-shop",//290
//			"toybox",//544
//			"axTLS", // 684
//			"financial",//771 
//			"busybox_1_28_0", // 998  			
  			/***************Median-scale******************** */
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
  			/*******************  Large-scale ***************** */
			 "busybox-1.18.0",//6796
			 "2.6.28.6-icse11", //6888
			 "uClinux-config", //11254
			 "buildroot", // 14910   		
	};

	gfr.t           = 2; // To generate results for t= X, t=0 means faults rate
	gfr.nbProds     = 100;
	gfr.outputDir   = "./output/";
	gfr.runs        = 30; 
//	gfr.algName     = "SAT4J";		
//	gfr.algName     = "PaD+SAT4J";		
	
//	gfr.algName     = "rSAT4J";		
//	gfr.algName     = "PaD+rSAT4J";	
	gfr.algName     = "PaD+rSAT4Jnew";	

//	gfr.algName     = "ProbSAT";
//	gfr.algName     = "PaD+ProbSAT";
	
	
	String fmFile = null;	
	for (int i = 0;i < fms.length;i++) {				

		fmFile = "./all_FM/Selected/" + fms[i] + ".dimacs"; 
		
		System.out.println(fmFile);
		SPL_sampler.getInstance().initializeModelSolversCalIndicators(fmFile,  gfr.t);
		
		gfr.computeTwiseCoverage(fmFile);	
//		gfr.computeFaultRate(fmFile); 
	} // main
  }
} 


