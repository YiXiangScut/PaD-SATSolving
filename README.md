# PaD-SATSolving
Code for "Sampling Configurations From Software Product Lines Via Probability-aware Diversification and SAT Solving"
The entry is spl/SPL_sampler.java/main

  		SPL_sampler.getInstance().sampling_rSAT4J(fmFile, outputDir, runs, nbProds); //rSAT4J
      
  		SPL_sampler.getInstance().sampling_PaDrSAT4J(fmFile, outputDir, runs, nbProds); //PaD+rSAT4J
      
  		SPL_sampler.getInstance().sampling_ProbSAT(fmFile, outputDir, runs, nbProds); //ProbSAT
      
  		SPL_sampler.getInstance().sampling_PaDProbSAT(fmFile, outputDir, runs, nbProds); //PaD+ProbSAT

Some parameters should be specified.

 	String outputDir = "./output/";  // output dir
  
  	int runs = 2; // How many runs
    
  	int nbProds = 100; // How many products (samples) returned (100, 500, 1000, or any number you want)
