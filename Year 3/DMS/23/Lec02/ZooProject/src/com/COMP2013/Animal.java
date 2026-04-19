package com.COMP2013;

public class Animal {
    private String species;
    private String nickname;

    public Animal(String species, String nickname){
        this.species = species;
        this.nickname = nickname;
    }

    public String getSpecies() {
        return species;
    }

    public String getNickname() {
        return nickname;
    }

    public String toString(){
        return species + "(" + nickname + ")";
    }
}
