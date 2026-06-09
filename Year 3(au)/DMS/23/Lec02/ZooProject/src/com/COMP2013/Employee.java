package com.COMP2013;

public abstract class Employee implements Employable {
    private String name;
    private int salary;

    protected Employee(String name, int salary) {
        this.name = name;
        this.salary = salary;
    }

    @Override
    public void setName(String name) {
        this.name = name;
    }

    @Override
    public String getName() {
        return name;
    }

    @Override
    public void setSalary(int salary) {
        this.salary = salary;
    }

    @Override
    public int getSalary() {
        return salary;
    }

}
