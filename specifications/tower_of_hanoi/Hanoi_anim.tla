---- MODULE Hanoi_anim ----
EXTENDS TLC, SVG, Sequences, Hanoi

\* Layout constants
TowerSpacing == 120
TowerBaseY == 200
TowerHeight == 150
DiskHeight == 15
BaseX == 60

\* Helper to decode which disks are on a tower (from bitwise representation)
\* Returns a sequence of disk sizes (powers of 2) in bottom-to-top order
DisksOnTower(towerValue) ==
    LET RECURSIVE FindDisks(_,_)
        FindDisks(value, maxDisk) ==
            IF maxDisk = 0 THEN <<>>
            ELSE IF value >= maxDisk 
                 THEN <<maxDisk>> \o FindDisks(value - maxDisk, maxDisk \div 2)
                 ELSE FindDisks(value, maxDisk \div 2)
    IN FindDisks(towerValue, 2^(D-1))

\* Color for each disk based on size
DiskColor(diskSize) ==
    CASE diskSize = 1 -> "#e57373"      \* Red for smallest
      [] diskSize = 2 -> "#81c784"      \* Green
      [] diskSize = 4 -> "#64b5f6"      \* Blue
      [] diskSize = 8 -> "#ffd54f"      \* Yellow
      [] diskSize = 16 -> "#ba68c8"     \* Purple
      [] diskSize = 32 -> "#4db6ac"     \* Teal
      [] diskSize = 64 -> "#ff8a65"     \* Orange
      [] OTHER -> "#90a4ae"             \* Gray for larger

\* Disk width based on size (log2 of size gives us the disk number)
DiskWidth(diskSize) ==
    LET RECURSIVE Log2(_)
        Log2(n) == IF n <= 1 THEN 0 ELSE 1 + Log2(n \div 2)
        diskNum == Log2(diskSize) + 1
    IN 20 + diskNum * 15

\* Draw a single disk at position
DrawDisk(x, y, diskSize) ==
    LET width == DiskWidth(diskSize)
    IN Rect(x - width \div 2, y, width, DiskHeight - 2,
            ("fill" :> DiskColor(diskSize) @@ 
             "stroke" :> "#333" @@ 
             "stroke-width" :> "1" @@
             "rx" :> "3"))

\* Draw all disks on a tower
DrawDisksOnTower(towerIdx) ==
    LET x == BaseX + (towerIdx - 1) * TowerSpacing
        disks == DisksOnTower(towers[towerIdx])
        diskElements == [i \in 1..Len(disks) |->
            DrawDisk(x, TowerBaseY - i * DiskHeight, disks[i])]
    IN Group(diskElements, <<>>)

\* Draw tower pole
DrawTowerPole(towerIdx) ==
    LET x == BaseX + (towerIdx - 1) * TowerSpacing
    IN Group(<<
        \* Pole
        Rect(x - 3, TowerBaseY - TowerHeight, 6, TowerHeight,
             ("fill" :> "#795548" @@ "stroke" :> "#333")),
        \* Base
        Rect(x - 40, TowerBaseY, 80, 8,
             ("fill" :> "#5d4037" @@ "stroke" :> "#333" @@ "rx" :> "2")),
        \* Tower label
        Text(x, TowerBaseY + 25, "Tower " \o ToString(towerIdx),
             ("text-anchor" :> "middle" @@ 
              "font-size" :> "12px" @@
              "fill" :> "#666"))
    >>, <<>>)

\* Success indicator
SuccessIndicator ==
    IF towers[N] = 2^D - 1 THEN
        Group(<<
            Rect(10, 10, 340, 30, 
                 ("fill" :> "#4caf50" @@ 
                  "stroke" :> "#2e7d32" @@
                  "rx" :> "5")),
            Text(180, 30, "SOLVED!",
                 ("text-anchor" :> "middle" @@ 
                  "font-size" :> "18px" @@
                  "font-weight" :> "bold" @@
                  "fill" :> "white"))
        >>, <<>>)
    ELSE
        Group(<<>>, <<>>)

\* Title
Title == Text(180, 15, "Tower of Hanoi - " \o ToString(D) \o " disks",
              ("text-anchor" :> "middle" @@ 
               "font-size" :> "14px" @@
               "font-weight" :> "bold" @@
               "fill" :> "#333"))

\* Step number
StepNumber == 
    Text(350, 240, "Step " \o ToString(TLCGet("level")),
         ("text-anchor" :> "end" @@ 
          "font-size" :> "12px" @@
          "font-family" :> "monospace" @@
          "fill" :> "#666"))

\* Main animation view
AnimView ==
    Group(<<Title, SuccessIndicator, StepNumber>> \o
          [i \in 1..N |-> DrawTowerPole(i)] \o
          [i \in 1..N |-> DrawDisksOnTower(i)],
          <<>>)

\* Wrap view in SVG document
AnimDoc == SVGDoc(AnimView, 0, 0, 360, 250, <<>>)

\* For TLC model checking (generates numbered frames)
AnimAlias ==
    [towers |-> towers] @@
    [_anim |-> SVGSerialize(AnimDoc, "Hanoi_anim_", TLCGet("level"))]

\* For interactive debugging (live preview)
AnimWatch ==
    SVGSerialize(AnimDoc, "Hanoi_anim", 0)
====
