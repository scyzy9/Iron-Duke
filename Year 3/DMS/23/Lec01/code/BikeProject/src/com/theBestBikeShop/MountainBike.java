package com.theBestBikeShop;

public class MountainBike extends Bicycle {
    private boolean frontSuspension;
    private boolean rearSuspension;

    public MountainBike(int gear, int speed, boolean frontSuspension, boolean rearSuspension) {
        super(gear, speed);
        this.frontSuspension = frontSuspension;
        this.rearSuspension = rearSuspension;
    }

    public boolean isFullSuspension() {
        return frontSuspension && rearSuspension;
    }

    @Override
    public void currentState() {
        System.out.println(
                "Gear: " + getGear() +
                        ", Speed: " + getSpeed() +
                        ", Light: " + (isLightOn() ? "On" : "Off") +
                        ", Full Suspension: " + (isFullSuspension() ? "Yes" : "No")
        );
    }
}
