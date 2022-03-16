/* GenerateTablesMain.java
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
 * modified under the terms of the GNU  General Public License
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

import java.io.IOException;

import jmetal.core.Algorithm;
import jmetal.experiments.Experiment;
import jmetal.experiments.Settings;
import jmetal.experiments.util.Friedman;
import jmetal.util.JMException;


public class GenerateTablesMain extends Experiment {

  /**
   * Configures the algorithms in each independent run
   * @param problemName The problem to solve
   * @param problemIndex
   * @throws ClassNotFoundException 
   */
  public void algorithmSettings(String problemName, 
  		                          int problemIndex, 
  		                          Algorithm[] algorithm) throws ClassNotFoundException {
    
  } // algorithmSettings

  /**
   * Main method
   * @param args
   * @throws JMException
   * @throws IOException
   */
  public static void main(String[] args) throws JMException, IOException {
    GenerateTablesMain exp = new GenerateTablesMain();

    exp.experimentName_ = "output";  

    exp.nproducts = 100; // the number of products
       
    exp.algorithmNameList_ = new String[]{	 
//	"SAT4JnoOrder",
//	 "PaD+SAT4JnoOrder",
    		
//    	"SAT4J",
//    	"PaD+SAT4J",
//    	"PaD+SAT4Jnew",
//    	
//        	"CheckingUnchangedVars",
    		
    	//-----R1-------
    	"rSAT4J",
    	"PaD+rSAT4Jnew",

        	

//    	-----R1----
//    	"ProbSATRerun",
//    	"PaD+ProbSATRerun",
    		
//    	"ProbSAT",
//    	"PaD+ProbSAT",
//        	"PaD+rSAT4J",
//    	"ProbSATWhileRepair",
//    	"PaD+ProbSATWhileRepair",
		};
    
    exp.problemList_ = new String[]{
    		
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
//  			/***************Median-scale******************** */
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
////  			 /*******************  Large-scale ***************** */
			 "busybox-1.18.0",//6796
			 "2.6.28.6-icse11", //6888
			 "uClinux-config", //11254
			 "buildroot", // 14910
			 "freetz", //31012	
    		};

    for (int i = 0;i<exp.problemList_.length;i++) {	
    	 exp.problemList_[i] =  exp.problemList_[i] + ".dimacs"; 	
    }
    	
    exp.indicatorList_ = new String[]{
//    		"Coverage",
//    		"MeanFaultRate", 
//    		"Nscore",    		
    		"invertedDist",
//    		"2wiseCoverage",
//    		"6wiseCoverage",
//    		"4wiseCoverage",
//    		"RUNTIME",
//    		"UnchangedRatio",
//    		"OriginalUnchangedRatio",
//    		"5wiseCoverage",
//    		"Extension",
//    		"STD",
    		};
    
    int numberOfAlgorithms = exp.algorithmNameList_.length;    
  
    exp.experimentBaseDirectory_ = "./" +  exp.experimentName_ ;
    
    exp.algorithmSettings_ = new Settings[numberOfAlgorithms];

    exp.independentRuns_ = 30;   

    exp.initExperiment();

    // Run the experiments
    int numberOfThreads ;

    exp.generateQualityIndicators() ;

    // Generate latex tables
    exp.generateLatexTables(false) ;    // generate tables without test symbols
//    exp.generateLatexTables(true) ;    // generate tables with test symbols, should perform the  Mann-Whitney U test first
    // Applying Friedman test
    Friedman test = new Friedman(exp);
//    test.executeTest("Coverage");
//    test.executeTest("HV");
//    test.executeTest("GSPREAD");
//    test.executeTest("IGD");
//    test.executeTest("RUNTIME");
  } // main
} // 


