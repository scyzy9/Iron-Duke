package com.COMP2013;

import java.util.ArrayList;

public class Compound{
    private String name;

    private ArrayList<Animal> animals = new ArrayList<>();

    public Compound(String name){
        this.name = name;
    }

    public void addAnimal(Animal a){
        animals.add(a);
    }

    public String getName(){
        return name;
    }

    public ArrayList<Animal> getAnimals(){
        return animals;
    }
}


