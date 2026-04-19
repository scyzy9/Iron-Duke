package com.COMP2013;

public abstract class Animal implements Maintainable{
    private String species;
    public Animal(String species){
        this.species = species;
    }
    public String getSpecies(){
        return species;
    }
}
