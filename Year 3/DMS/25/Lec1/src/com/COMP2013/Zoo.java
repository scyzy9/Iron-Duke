package com.COMP2013
import java.util.ArrayList;

public class Zoo{
    private String location;
    private int numCompounds;

    public static int numZoos = 0;
    private final int zooID;

    private ArrayList<Compound> compounds;
    
    public zoo(){
        this("Unknown",30);
    }

    public Zoo(String location, int numCompounds){
        this.location = location;
        this.numCompounds = numCompounds;\

        numZoos++;
        this.zooID = numZoos;

        compounds = new ArrayList<>();
    }

    public String getLocation(){
        return location;
    }

    public void setLocation(String location){
        this.location = location;
    }

    public int getNumCompounds(){
        return numCompounds;
    }

    public int getZooID(){
        return zooID;
    }

    public void buildNewCompound(){
        numCompounds++;
        compounds.add(new Compound("Compound-" + numCompounds));
    }

    public void addCompound(Compound c){
        compounds.add(c);
    }

    public ArrayList<Compound> getCompounds(){
        return compounds;
    }

    public String printInfo(){
        return "[Zoo#" + zooID + "]" + location + "| compounds" + numCompounds;
    }
    
    public static void main(String[] args)
    {
        Zoo z1 = new Zoo();
        Zoo z2 = new Zoo("London" , 5);
        System.out.println(z1.printInfo());
        System.out.println(z2.printInfo());
        System.out.println("Total Zoos:" + Zoo.numZoos);
    }
    
}