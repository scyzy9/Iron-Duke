package com.COMP2013.lab3;

import java.util.concurrent.ThreadLocalRandom;

public class DummyPhone implements Phone {
    @Override
    public int makeCall(String number) throws InterruptedException {
        int secs = ThreadLocalRandom.current().nextInt(2, 7);
        Thread.sleep(secs*1000L);
        return secs;
    }
}
