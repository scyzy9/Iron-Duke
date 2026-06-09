import java.util.Random;

public class Main {

    static int c;
    static Random rnd = new Random();

    static final boolean STUDY_INTLOG = true; 
    static final int MAX_N = 999;              
    static final int NUM_RUNS = 99;           
    static final int MAX_VAL = 999;            

    enum InitMode { RAND, INC, RAND_INC }
    static final InitMode INIT_MODE = InitMode.RAND; 
    // =================================

    public static void main(String[] args) {

        if (STUDY_INTLOG) {
            System.out.println("n,c");
            for (int n = 1; n <= MAX_N; n *= 2) {
                c = 0;
                intLog(n);
                System.out.println(n + "," + c);
            }
        } else {
            System.out.println("n,worst,best,avg");

            for (int n = 1; n <= MAX_N; n *= 2) {   
                int[] A = new int[n];

                double worst = 0.0;
                double best = Double.POSITIVE_INFINITY;
                double sum = 0.0;

                for (int run = 0; run < NUM_RUNS; run++) {
                    initArray(A, MAX_VAL);

                    c = 0;
                    arrayMax(A);

                    if (c > worst) worst = c;
                    if (c < best)  best  = c;
                    sum += c;
                }

                double avg = sum / NUM_RUNS;
                System.out.println(n + "," + worst + "," + best + "," + avg);
            }
        }
    }


    static int intLog(int n) {
        int m = 0;
        c += 1;               // assignment: m=0

        while (n >= 2) {
            c += 1;           // comparison: n>=2

            n = n / 2;
            c += 2;           // division + assignment

            m++;
            c += 1;           // increment
        }
        c += 1;               // final failed comparison (n>=2)
        c += 1;               // return
        return m;
    }

    static int arrayMax(int[] A) {
        int n = A.length;
        c += 1;               // assignment: n=A.length

        if (n == 0) {
            c += 1;           // comparison
            return -1;
        }
        c += 1;               // comparison for n==0 

        int currentMax = A[0];
        c += 2;               // A[0] access + assignment

        for (int p = 1; p < n; p++) {
            c += 1;           // loop comparison: p<n

            // if (A[p] > currentMax)
            c += 2;           // A[p] access + comparison
            if (A[p] > currentMax) {
                currentMax = A[p];
                c += 2;       // A[p] access + assignment
            }

            c += 1;           // p++ increment
        }

        c += 1;               // final failed loop comparison
        c += 1;               // return
        return currentMax;
    }

    static void initArray(int[] A, int maxVal) {
        switch (INIT_MODE) {
            case RAND -> randInit(A, maxVal);
            case INC -> incInit(A);
            case RAND_INC -> randIncInit(A, maxVal);
        }
    }

    static void randInit(int[] A, int max) {
        for (int i = 0; i < A.length; i++) {
            A[i] = rnd.nextInt(max);
        }
    }

    static void incInit(int[] A) {
        for (int i = 0; i < A.length; i++) {
            A[i] = i;
        }
    }

    static void randIncInit(int[] A, int max) {
        int base = 0;
        for (int i = 0; i < A.length; i++) {
            base += rnd.nextInt(max);
            A[i] = base;
        }
    }
}