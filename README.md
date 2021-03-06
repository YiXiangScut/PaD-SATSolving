# PaD-SATSolving
Sampling Configurations From Software Product Lines Via Probability-aware Diversification and SAT Solving
# About this project
This project is developed based on Java language. Please make sure that Java virtual machine is installed in your computer. Please add all Jar files in ./dist/lib into Java build path.
# How to run?
Step 1: The entry of this project is src/spl/SPL_sampler/main. You need to specify the following:

	String [] fms = { // Feature models (FM) to be sampled
			"CounterStrikeSimpleFeatureModel", // the first FM
			"HiPAcc",// the second one, etc.
			};    	
	 
 	String outputDir = "./output/";  // output dir
  	int runs =30; // How many runs
  	int nbProds = 100; // How many products (samples) returned (100, 500, 1000, or any number you want)

  	SPL_sampler.getInstance().sampling_rSAT4J(fmFile, outputDir, runs, nbProds); //rSAT4J
  	SPL_sampler.getInstance().sampling_PaDrSAT4J(fmFile, outputDir, runs, nbProds); //PaD+rSAT4J 
  	SPL_sampler.getInstance().sampling_ProbSAT(fmFile, outputDir, runs, nbProds); //ProbSAT
  	SPL_sampler.getInstance().sampling_PaDProbSAT(fmFile, outputDir, runs, nbProds); //PaD+ProbSAT

After running src/spl/SPL_sampler.java, you will get a folder, output, containing generated samples.

Step 2: To get the performance metric spread, you need to run src/spl/GenerateSpread.java. In the main function of this java file, you need 
to configure the following:

	gfr.nbProds     = 100;
	gfr.outputDir   = "./output/";  
	gfr.runs        = 30;	
	gfr.algName     = "rSAT4J";// Specify the name of the sampler
	
Note that spread is stored as "invertedDist" in the hard disk.

Step 3: To get latex tables, please run src/spl/GenerateTablesMain.java. 

Please feel free to contact Dr. Yi Xiang at gzhuxiang_yi@163.com if you have any questions. 
