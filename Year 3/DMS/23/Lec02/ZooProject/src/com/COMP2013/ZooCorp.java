package com.COMP2013;

import java.util.ArrayList;

public class ZooCorp {
    private String corpName;
    private ArrayList<Zoo> zoos = new ArrayList<>();
    private ArrayList<Employable> employees = new ArrayList<>();

    public ZooCorp(String corpName, Zoo firstZoo){
        this.corpName = corpName;
        addZoo(firstZoo);
    }
    public void addZoo(Zoo z){
        zoos.add(z);
    }
    public void addEmployee(Employable e)
    {
        employees.add(e);
    }

    public ArrayList<Zoo> getZoos(){
        return zoos;
    }

    public ArrayList<Employable> getEmployees(){
        return employees;
    }

    public String getCorpName(){
        return corpName;
    }
}
