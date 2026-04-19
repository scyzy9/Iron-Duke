package com.COMP2013;

public class Admin extends Employee{
    public Admin(String name, int salary) {
        super(name, salary);
    }

    @Override
    public int calculateChristmasBonus() {
        return (int)Math.round(getSalary()*0.08);
    }
    @Override
    public String toString() {
        return "Admin{name = %s , salary = %d , bonus = %d}".formatted(getName(),getSalary(),calculateChristmasBonus());
    }
}
