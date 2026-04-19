package com.COMP2013;

import java.util.ArrayList;

public class Zoo {
    private String location;
    private int numCompounds;         // 围场数量
    private int zooID;                // 唯一ID（由静态计数派生）

    // 所有 Zoo 实例共享的计数器
    public static int numZoos = 0;

    // 围场集合
    private ArrayList<Compound> compounds;

    // 默认构造：设置一个默认围场数（如 30）
    public Zoo() {
        this("Unknown", 30);
    }

    // 带参构造
    public Zoo(String location, int numCompounds) {
        this.location = location;
        this.numCompounds = numCompounds;

        // 实例化集合；创建时根据数量生成 Compound
        this.compounds = new ArrayList<>();

        // 递增共享计数，并据此赋予唯一 ID
        numZoos++;
        this.zooID = numZoos;

        // 生成初始围场对象
        for (int i = 0; i < numCompounds; i++) {
            addCompound(new Compound("Compound-" + (i + 1)));
        }
    }

    // 围场+1
    public void buildNewCompound() {
        addCompound(new Compound("Compound-" + (compounds.size() + 1)));
        this.numCompounds = compounds.size();
    }

    // 添加围场
    public void addCompound(Compound c) {
        this.compounds.add(c);
    }

    // 打印信息（返回字符串以便复用/测试）
    public String printInfo() {
        return String.format("Zoo #%d @ %s, compounds=%d",
                zooID, location, numCompounds);
    }

    // getters / setters（按需最小化）
    public String getLocation() { return location; }
    public void setLocation(String location) { this.location = location; }

    public int getNumCompounds() { return numCompounds; }

    public int getZooID() { return zooID; } // 仅 getter，不暴露 setter，保持唯一性与不可变性

    public ArrayList<Compound> getCompounds() { return compounds; }
}
