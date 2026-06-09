package com.COMP2013;

public class ZooApp {
    public static void main(String[] args) {
        Zoo z1 = new Zoo();
        Zoo z2 = new Zoo("Tokyo",3);
        Zoo z3 = new Zoo("London",5);
        Zoo z4 = new Zoo("New York",4);
        Zoo z5 = new Zoo("Paris",2);

        z2.buildNewCompound();
        System.out.println(z1.printInfo());
        System.out.println(z2.printInfo());
        System.out.println(z3.printInfo());
        System.out.println(z4.printInfo());
        System.out.println(z5.printInfo());
        System.out.println("Total zoos created = " + Zoo.numZoos);

        Compound c = z2.getCompounds().get(0);
        c.addAnimal(new Animal ("Lion","Simba"));
        c.addAnimal(new Animal ("Giraffe" , "LongNeck"));

        ZooCorp corp = new ZooCorp("ZooCorp Intl" , z1);
        corp.addZoo(z2);
        corp.addZoo(z3);
        corp.addZoo(z4);
        corp.addZoo(z5);

        Zookeeper zk = new Zookeeper("Alice",3000);
        Admin ad = new Admin("Bob",4000);
        corp.addEmployee(zk);
        corp.addEmployee(ad);

        System.out.println("\n== "+corp.getCorpName() + " ==");
        for (Employable e : corp.getEmployees()){
            System.out.println(e.getClass().getSimpleName() + " -> name = " + e.getName()
            + ", salary= " + e.getSalary()
            + ", bonus= " + e.calculateChristmasBonus());
        }
    }
}
