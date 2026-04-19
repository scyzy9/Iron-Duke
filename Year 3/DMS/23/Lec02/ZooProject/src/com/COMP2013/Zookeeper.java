package com.COMP2013;

public class Zookeeper extends Employee{
    public Zookeeper(String name, int salary) {
        super(name, salary);
    }

    @Override
    public int calculateChristmasBonus(){
        return (int)Math.round(getSalary()*0.05) + 100;
    }

    @Override
    public String toString(){
        return "Zookeeper{name = %s, salary = %d, bonus = %d".formatted(getName(),getSalary(),calculateChristmasBonus());
    }
}
