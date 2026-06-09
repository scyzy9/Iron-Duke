import java.util.Random;

public class Main {

    private static final Random RND = new Random(2054);

    private static class IntPair {
        int x;
        int y;

        IntPair(int value, int originalIndex) {
            this.x = value;
            this.y = originalIndex;
        }
    }

    private static class ListNode {
        IntPair data;
        ListNode next;

        ListNode(IntPair data) {
            this.data = data;
        }
    }

    private static class SortStats {
        final String name;
        long comparisons;
        long swaps;
        long shifts;

        SortStats(String name) {
            this.name = name;
        }

        void add(SortStats other) {
            comparisons += other.comparisons;
            swaps += other.swaps;
            shifts += other.shifts;
        }
    }

    private static class ListSortResult {
        final ListNode head;
        final SortStats stats;

        ListSortResult(ListNode head, SortStats stats) {
            this.head = head;
            this.stats = stats;
        }
    }

    @FunctionalInterface
    private interface ArraySorter {
        SortStats sort(IntPair[] array);
    }

    @FunctionalInterface
    private interface ListSorter {
        ListSortResult sort(ListNode head);
    }

    public static void main(String[] args) {
        int[] sample = {54, 53, 52, 54, 50, 53, 52};
        int[] sizes = {8, 16, 32, 64};
        int experimentRuns = 20;

        System.out.println("COMP2054 Week 6 - Simple Sorting Lab");
        runArrayDemonstrations(sample);
        runScalingExperiment("Bubble sort", Main::bubbleSort, sizes, experimentRuns);
        runScalingExperiment("Selection sort", Main::selectionSort, sizes, experimentRuns);
        runScalingExperiment("Insertion sort", Main::insertionSort, sizes, experimentRuns);
        runAdaptiveExperiment("Bubble sort", Main::bubbleSort, 24, experimentRuns);
        runAdaptiveExperiment("Selection sort", Main::selectionSort, 24, experimentRuns);
        runAdaptiveExperiment("Insertion sort", Main::insertionSort, 24, experimentRuns);
        runRecursiveDemonstrations(sample);
        runLinkedListDemonstrations(sample);
    }

    private static void runArrayDemonstrations(int[] sample) {
        System.out.println("\n=== Array sorts and stability ===");
        runArrayDemo("Bubble sort", sample, Main::bubbleSort);
        runArrayDemo("Selection sort", sample, Main::selectionSort);
        runArrayDemo("Stable selection sort", sample, Main::stableSelectionSort);
        runArrayDemo("Insertion sort", sample, Main::insertionSort);
    }

    private static void runScalingExperiment(String name, ArraySorter sorter, int[] sizes, int runs) {
        System.out.println("\n=== Scaling on random arrays: " + name + " ===");
        for (int size : sizes) {
            SortStats totals = new SortStats(name);
            for (int run = 0; run < runs; run++) {
                int[] values = randomValues(size);
                totals.add(sorter.sort(toPairs(values)));
            }
            printAverageStats(size, runs, totals);
        }
    }

    private static void runAdaptiveExperiment(String name, ArraySorter sorter, int size, int runs) {
        System.out.println("\n=== Adaptive check: " + name + " (n=" + size + ") ===");
        printPatternAverages("sorted      ", sorter, runs, size, "sorted");
        printPatternAverages("nearlySorted", sorter, runs, size, "nearly");
        printPatternAverages("random      ", sorter, runs, size, "random");
        printPatternAverages("reversed    ", sorter, runs, size, "reversed");
    }

    private static void runRecursiveDemonstrations(int[] sample) {
        System.out.println("\n=== Recursive versions ===");
        runArrayDemo("Recursive bubble sort", sample, Main::bubbleSortRecursive);
        runArrayDemo("Recursive selection sort", sample, Main::selectionSortRecursive);
        runArrayDemo("Recursive insertion sort", sample, Main::insertionSortRecursive);
    }

    private static void runLinkedListDemonstrations(int[] sample) {
        System.out.println("\n=== Linked-list versions ===");
        runListDemo("Linked-list bubble sort", sample, Main::bubbleSortList);
        runListDemo("Linked-list selection sort", sample, Main::selectionSortList);
        runListDemo("Linked-list insertion sort", sample, Main::insertionSortList);
    }

    private static void runArrayDemo(String title, int[] values, ArraySorter sorter) {
        IntPair[] pairs = toPairs(values);
        System.out.println("\n" + title);
        System.out.print("START ");
        printArray(pairs);
        System.out.println();

        SortStats stats = sorter.sort(pairs);

        System.out.print("END   ");
        printArray(pairs);
        System.out.println();
        printOutcome(pairs, stats);
    }

    private static void runListDemo(String title, int[] values, ListSorter sorter) {
        ListNode head = buildList(values);
        System.out.println("\n" + title);
        System.out.print("START ");
        printList(head);
        System.out.println();

        ListSortResult result = sorter.sort(head);

        System.out.print("END   ");
        printList(result.head);
        System.out.println();
        printOutcome(result.head, result.stats);
    }

    private static void printPatternAverages(String label, ArraySorter sorter, int runs, int size, String pattern) {
        SortStats totals = new SortStats(label.trim());
        for (int run = 0; run < runs; run++) {
            int[] values = createPattern(pattern, size);
            totals.add(sorter.sort(toPairs(values)));
        }
        System.out.printf(
            "%s avg comparisons=%8.2f avg swaps=%8.2f avg shifts=%8.2f%n",
            label,
            average(totals.comparisons, runs),
            average(totals.swaps, runs),
            average(totals.shifts, runs)
        );
    }

    private static void printAverageStats(int size, int runs, SortStats totals) {
        System.out.printf(
            "n=%3d avg comparisons=%8.2f avg swaps=%8.2f avg shifts=%8.2f%n",
            size,
            average(totals.comparisons, runs),
            average(totals.swaps, runs),
            average(totals.shifts, runs)
        );
    }

    private static double average(long total, int runs) {
        return total / (double) runs;
    }

    private static SortStats bubbleSort(IntPair[] array) {
        SortStats stats = new SortStats("Bubble sort");
        for (int end = array.length - 1; end > 0; end--) {
            boolean swapped = false;
            for (int i = 0; i < end; i++) {
                stats.comparisons++;
                if (array[i].x > array[i + 1].x) {
                    swap(array, i, i + 1);
                    stats.swaps++;
                    swapped = true;
                }
            }
            if (!swapped) {
                break;
            }
        }
        return stats;
    }

    private static SortStats bubbleSortRecursive(IntPair[] array) {
        SortStats stats = new SortStats("Recursive bubble sort");
        bubbleSortRecursive(array, array.length, stats);
        return stats;
    }

    private static void bubbleSortRecursive(IntPair[] array, int length, SortStats stats) {
        if (length <= 1) {
            return;
        }
        boolean swapped = bubblePassRecursive(array, length, stats);
        if (swapped) {
            bubbleSortRecursive(array, length - 1, stats);
        }
    }

    private static boolean bubblePassRecursive(IntPair[] array, int length, SortStats stats) {
        if (length <= 1) {
            return false;
        }
        boolean swapped = bubblePassRecursive(array, length - 1, stats);
        stats.comparisons++;
        if (array[length - 2].x > array[length - 1].x) {
            swap(array, length - 2, length - 1);
            stats.swaps++;
            return true;
        }
        return swapped;
    }

    private static SortStats selectionSort(IntPair[] array) {
        SortStats stats = new SortStats("Selection sort");
        for (int start = 0; start < array.length - 1; start++) {
            int minIndex = start;
            for (int scan = start + 1; scan < array.length; scan++) {
                stats.comparisons++;
                if (array[scan].x < array[minIndex].x) {
                    minIndex = scan;
                }
            }
            if (minIndex != start) {
                swap(array, start, minIndex);
                stats.swaps++;
            }
        }
        return stats;
    }

    private static SortStats stableSelectionSort(IntPair[] array) {
        SortStats stats = new SortStats("Stable selection sort");
        for (int start = 0; start < array.length - 1; start++) {
            int minIndex = start;
            for (int scan = start + 1; scan < array.length; scan++) {
                stats.comparisons++;
                if (array[scan].x < array[minIndex].x) {
                    minIndex = scan;
                }
            }

            if (minIndex != start) {
                IntPair minValue = array[minIndex];
                while (minIndex > start) {
                    array[minIndex] = array[minIndex - 1];
                    stats.shifts++;
                    minIndex--;
                }
                array[start] = minValue;
                stats.shifts++;
            }
        }
        return stats;
    }

    private static SortStats selectionSortRecursive(IntPair[] array) {
        SortStats stats = new SortStats("Recursive selection sort");
        selectionSortRecursive(array, 0, stats);
        return stats;
    }

    private static void selectionSortRecursive(IntPair[] array, int start, SortStats stats) {
        if (start >= array.length - 1) {
            return;
        }
        int minIndex = findMinIndexRecursive(array, start, start + 1, stats);
        if (minIndex != start) {
            swap(array, start, minIndex);
            stats.swaps++;
        }
        selectionSortRecursive(array, start + 1, stats);
    }

    private static int findMinIndexRecursive(IntPair[] array, int currentMin, int scan, SortStats stats) {
        if (scan >= array.length) {
            return currentMin;
        }
        stats.comparisons++;
        if (array[scan].x < array[currentMin].x) {
            currentMin = scan;
        }
        return findMinIndexRecursive(array, currentMin, scan + 1, stats);
    }

    private static SortStats insertionSort(IntPair[] array) {
        SortStats stats = new SortStats("Insertion sort");
        for (int i = 1; i < array.length; i++) {
            IntPair key = array[i];
            int j = i - 1;

            while (j >= 0) {
                stats.comparisons++;
                if (array[j].x <= key.x) {
                    break;
                }
                array[j + 1] = array[j];
                stats.shifts++;
                j--;
            }

            array[j + 1] = key;
            stats.shifts++;
        }
        return stats;
    }

    private static SortStats insertionSortRecursive(IntPair[] array) {
        SortStats stats = new SortStats("Recursive insertion sort");
        insertionSortRecursive(array, array.length, stats);
        return stats;
    }

    private static void insertionSortRecursive(IntPair[] array, int length, SortStats stats) {
        if (length <= 1) {
            return;
        }
        insertionSortRecursive(array, length - 1, stats);
        IntPair last = array[length - 1];
        insertRecursively(array, length - 2, last, stats);
    }

    private static void insertRecursively(IntPair[] array, int index, IntPair value, SortStats stats) {
        if (index < 0) {
            array[0] = value;
            stats.shifts++;
            return;
        }

        stats.comparisons++;
        if (array[index].x <= value.x) {
            array[index + 1] = value;
            stats.shifts++;
            return;
        }

        array[index + 1] = array[index];
        stats.shifts++;
        insertRecursively(array, index - 1, value, stats);
    }

    private static ListSortResult bubbleSortList(ListNode head) {
        SortStats stats = new SortStats("Linked-list bubble sort");
        if (head == null || head.next == null) {
            return new ListSortResult(head, stats);
        }

        boolean swapped;
        ListNode end = null;
        do {
            swapped = false;
            ListNode current = head;
            while (current.next != end) {
                stats.comparisons++;
                if (current.data.x > current.next.data.x) {
                    IntPair temp = current.data;
                    current.data = current.next.data;
                    current.next.data = temp;
                    stats.swaps++;
                    swapped = true;
                }
                current = current.next;
            }
            end = current;
        } while (swapped);

        return new ListSortResult(head, stats);
    }

    private static ListSortResult selectionSortList(ListNode head) {
        SortStats stats = new SortStats("Linked-list selection sort");
        for (ListNode start = head; start != null; start = start.next) {
            ListNode minNode = start;
            for (ListNode scan = start.next; scan != null; scan = scan.next) {
                stats.comparisons++;
                if (scan.data.x < minNode.data.x) {
                    minNode = scan;
                }
            }
            if (minNode != start) {
                IntPair temp = start.data;
                start.data = minNode.data;
                minNode.data = temp;
                stats.swaps++;
            }
        }
        return new ListSortResult(head, stats);
    }

    private static ListSortResult insertionSortList(ListNode head) {
        SortStats stats = new SortStats("Linked-list insertion sort");
        ListNode sortedHead = null;
        ListNode current = head;

        while (current != null) {
            ListNode next = current.next;
            current.next = null;
            sortedHead = insertNodeIntoSortedList(sortedHead, current, stats);
            current = next;
        }

        return new ListSortResult(sortedHead, stats);
    }

    private static ListNode insertNodeIntoSortedList(ListNode sortedHead, ListNode node, SortStats stats) {
        if (sortedHead == null) {
            stats.shifts++;
            return node;
        }

        stats.comparisons++;
        if (node.data.x < sortedHead.data.x) {
            node.next = sortedHead;
            stats.shifts++;
            return node;
        }

        ListNode current = sortedHead;
        while (current.next != null) {
            stats.comparisons++;
            if (current.next.data.x > node.data.x) {
                break;
            }
            current = current.next;
        }

        node.next = current.next;
        current.next = node;
        stats.shifts++;
        return sortedHead;
    }

    private static int[] createPattern(String pattern, int size) {
        switch (pattern) {
            case "sorted":
                return sortedValues(size);
            case "nearly":
                return nearlySortedValues(size);
            case "reversed":
                return reversedValues(size);
            default:
                return randomValues(size);
        }
    }

    private static int[] randomValues(int size) {
        int[] values = new int[size];
        int bound = Math.max(4, size / 2 + 1);
        for (int i = 0; i < size; i++) {
            values[i] = 10 * size + RND.nextInt(bound);
        }
        return values;
    }

    private static int[] sortedValues(int size) {
        int[] values = new int[size];
        for (int i = 0; i < size; i++) {
            values[i] = i;
        }
        return values;
    }

    private static int[] reversedValues(int size) {
        int[] values = new int[size];
        for (int i = 0; i < size; i++) {
            values[i] = size - i;
        }
        return values;
    }

    private static int[] nearlySortedValues(int size) {
        int[] values = sortedValues(size);
        if (size < 2) {
            return values;
        }
        int swaps = Math.max(1, size / 8);
        for (int i = 0; i < swaps; i++) {
            int left = RND.nextInt(size - 1);
            int right = left + 1;
            int temp = values[left];
            values[left] = values[right];
            values[right] = temp;
        }
        return values;
    }

    private static IntPair[] toPairs(int[] values) {
        IntPair[] pairs = new IntPair[values.length];
        for (int i = 0; i < values.length; i++) {
            pairs[i] = new IntPair(values[i], i);
        }
        return pairs;
    }

    private static ListNode buildList(int[] values) {
        ListNode head = null;
        ListNode tail = null;
        for (int i = 0; i < values.length; i++) {
            ListNode node = new ListNode(new IntPair(values[i], i));
            if (head == null) {
                head = node;
                tail = node;
            } else {
                tail.next = node;
                tail = node;
            }
        }
        return head;
    }

    private static void swap(IntPair[] array, int left, int right) {
        IntPair temp = array[left];
        array[left] = array[right];
        array[right] = temp;
    }

    private static boolean isSorted(IntPair[] array) {
        for (int i = 1; i < array.length; i++) {
            if (array[i - 1].x > array[i].x) {
                return false;
            }
        }
        return true;
    }

    private static boolean isStable(IntPair[] array) {
        for (int i = 1; i < array.length; i++) {
            if (array[i - 1].x == array[i].x && array[i - 1].y > array[i].y) {
                return false;
            }
        }
        return true;
    }

    private static boolean isSorted(ListNode head) {
        for (ListNode current = head; current != null && current.next != null; current = current.next) {
            if (current.data.x > current.next.data.x) {
                return false;
            }
        }
        return true;
    }

    private static boolean isStable(ListNode head) {
        for (ListNode current = head; current != null && current.next != null; current = current.next) {
            if (current.data.x == current.next.data.x && current.data.y > current.next.data.y) {
                return false;
            }
        }
        return true;
    }

    private static void printArray(IntPair[] array) {
        System.out.print("[[");
        for (IntPair pair : array) {
            System.out.print(" " + pair.x + "(" + pair.y + ")");
        }
        System.out.print(" ]]");
    }

    private static void printList(ListNode head) {
        System.out.print("[[");
        for (ListNode current = head; current != null; current = current.next) {
            System.out.print(" " + current.data.x + "(" + current.data.y + ")");
        }
        System.out.print(" ]]");
    }

    private static void printOutcome(IntPair[] array, SortStats stats) {
        System.out.println(
            "RESULT sorted=" + isSorted(array)
            + " stable=" + isStable(array)
            + " comparisons=" + stats.comparisons
            + " swaps=" + stats.swaps
            + " shifts=" + stats.shifts
        );
    }

    private static void printOutcome(ListNode head, SortStats stats) {
        System.out.println(
            "RESULT sorted=" + isSorted(head)
            + " stable=" + isStable(head)
            + " comparisons=" + stats.comparisons
            + " swaps=" + stats.swaps
            + " shifts=" + stats.shifts
        );
    }
}
