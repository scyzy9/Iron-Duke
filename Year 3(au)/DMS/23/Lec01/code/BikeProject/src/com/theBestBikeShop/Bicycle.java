package com.theBestBikeShop;

public class Bicycle {
    private int gear;
    private int speed;
    private boolean lightOn;

    // 构造方法（Constructor）
    public Bicycle(int gear, int speed) {
        this.gear = gear;
        this.speed = speed;
        this.lightOn = false; // 默认关灯
    }

    // 改变速度
    public void changeSpeed(int newSpeed) {
        this.speed = newSpeed;
    }

    // 切换灯光状态
    public void switchLightStatus() {
        lightOn = !lightOn;
    }

    // 输出当前状态
    public void currentState() {
        System.out.println("Gear: " + gear + ", Speed: " + speed + ", Light: " + (lightOn ? "On" : "Off"));
    }

    // Getter / Setter
    public int getGear() { return gear; }
    public int getSpeed() { return speed; }
    public boolean isLightOn() { return lightOn; }
}
