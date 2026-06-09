package com.COMP2013

import java.util.ArrayList;

public class ZooCorp{
    private ArrayList<Zoo> zoos = new ArrayList<>();
    private ArrayList<Employable> employees = new ArrayList<>();

    public ZooCorp(Zoo initial){
        addZoo(initial);
    }
    
    public void addZoo(Zoo z){
        zoos.add(z);
    }

    public void hire(Employable e){
        employees.add(e);
    }

    public ArrayList<Zoo> getZoos(){
        return Zoos;
    }

    public ArrayList<Employable> getEmployees(){
        return employees;
    }
}