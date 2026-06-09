package com.theBestBikeShop;

public class BikeApp {
    public static void main(String[] args) {
        // 创建普通自行车
        Bicycle bike1 = new Bicycle(3, 15);
        bike1.switchLightStatus();
        bike1.changeSpeed(20);
        bike1.currentState();

        // 创建山地车（全避震）
        MountainBike mtb1 = new MountainBike(5, 25, true, true);
        mtb1.switchLightStatus();
        mtb1.currentState();

        // 创建山地车（非全避震）
        MountainBike mtb2 = new MountainBike(4, 18, true, false);
        mtb2.currentState();
    }
}
