package nl.ou.im9906;

import org.junit.Test;

import java.lang.reflect.InvocationTargetException;
import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.Map;

import static nl.ou.im9906.ClassInvariantTestHelper.assertClassInvariants;
import static nl.ou.im9906.ReflectionUtils.getValueByFieldName;
import static nl.ou.im9906.ReflectionUtils.getValueByStaticFieldName;
import static nl.ou.im9906.ReflectionUtils.hash;
import static nl.ou.im9906.ReflectionUtils.invokeMethodWithParams;
import static org.junit.Assert.fail;

/**
 * Tests the JML specifications of the {@link IdentityHashMap#put(Object, Object)}
 * method in relation to a possible bug.
 */
public class IdentityHashMapBugInPutTest {

    private IdentityHashMap<Object, Object> map;

    @Test
    public void testTooManyPutsCausesInfiniteLoopInPut()
            throws NoSuchFieldException, IllegalAccessException, NoSuchClassException {
        // Initialize map and break invariant by filling it up
        initAndBreakInvariant();

        // Another put() will cause an infinite loop
        System.out.println("TEST: Executing put(new Object, null) on a full map ...");
        map.put(new Object(), null);
    }

    @Test
    public void testTooManyPutsCausesInfiniteLoopInGet()
            throws NoSuchFieldException, IllegalAccessException, NoSuchClassException {
        // Initialize map and break invariant by filling it up
        initAndBreakInvariant();

        // Executing get() will cause an infinite loop
        System.out.println("Executing get() on a full map ...");
        map.get(new Object());
    }

    @Test
    public void testTooManyPutsCausesInfiniteLoopInContainsKey()
            throws NoSuchFieldException, IllegalAccessException, NoSuchClassException {
        // Initialize map and break invariant by filling it up
        initAndBreakInvariant();

        // Executing containsKey() will cause an infinite loop
        System.out.println("Executing containsKey() on a full map ...");
        map.containsKey(new Object());
    }

    @Test
    public void testTooManyPutsCausesInfiniteLoopInContainsMapping()
            throws NoSuchFieldException, IllegalAccessException,
            NoSuchClassException, InvocationTargetException,
            NoSuchMethodException {
        // Initialize map and break invariant by filling it up
        initAndBreakInvariant();

        // Executing containsMapping() will cause an infinite loop
        System.out.println("Executing containsMapping() on a full map ...");
        invokeMethodWithParams(map, "containsMapping", new Object(), new Object());
    }

    @Test
    public void testTooManyPutsCausesInfiniteLoopInPutAll()
            throws NoSuchFieldException, IllegalAccessException, NoSuchClassException {
        // Initialize map and break invariant by filling it up
        initAndBreakInvariant();

        // Executing putAll() will cause an infinite loop
        final Map<Object, Object> addMap = new HashMap<>();
        addMap.put(new Object(), null);
        System.out.println("Executing putAll() on a full map ...");
        map.putAll(addMap);
    }

    @Test
    public void testTooManyPutsCausesInfiniteLoopInRemove()
            throws NoSuchFieldException, IllegalAccessException, NoSuchClassException {
        // Initialize map and break invariant by filling it up
        initAndBreakInvariant();

        // Executing remove() will cause an infinite loop
        System.out.println("Executing remove() on a full map ...");
        map.remove(new Object());
    }

    // Initializes an IdentityHashMap, and puts entries in every slot of the map, breaking the
    // class invariant (two clauses, see output).
    private void initAndBreakInvariant()
            throws NoSuchFieldException, IllegalAccessException, NoSuchClassException {
        final int maxCapacity = (int) getValueByStaticFieldName(IdentityHashMap.class, "MAXIMUM_CAPACITY");
        map = new IdentityHashMap<Object, Object>(Integer.MAX_VALUE);

        // Add MAXIMUM_CAPACIY - 2 unique elements to the map
        for (int i = 0; i < maxCapacity - 2; i++) {
            map.put(new Object(), null);
        }

        // At this point, there are two empty entries. The class invariant still holds
        assertClassInvariants(map);

        // Now, keep adding entries, and ignore the IllegalStateExceptions thrown by resize().
        // The class invariant will be violated. This will cause several methods to loop
        // infinitely when searching for a non-existent key.
        while (map.size() < maxCapacity) {
            // Print the state beforehand
            System.out.println("");
            printState(map);
            System.out.println("Executing put(new Object(), null");

            // Try to put an entry into the map
            try {
                map.put(new Object(), null);
                fail("No exception was thrown. This was not expected.");
            } catch (IllegalStateException e) {
                System.out.println("IllegalStateException occurred as expected (via resize).");
            }

            // Print the state afterwards
            printState(map);
        }
    }

    // Prints the state of a map
    private void printState(IdentityHashMap<Object, Object> map)
            throws NoSuchFieldException, IllegalAccessException, NoSuchClassException {
        final int maxCapacity = (int) getValueByStaticFieldName(IdentityHashMap.class, "MAXIMUM_CAPACITY");
        final Object[] table = (Object[]) getValueByFieldName(map, "table");
        final int threshold = (int) getValueByFieldName(map, "threshold");
        boolean isClassInvariantViolated = false;
        try {
            assertClassInvariants(map);
        } catch (AssertionError e) {
            isClassInvariantViolated = true;
        }

        System.out.println("Current state of " + map.getClass().getSimpleName());
        System.out.println("- size = " + map.size());
        System.out.println("- table.length = " + table.length);
        System.out.println("- threshold = " + threshold);
        System.out.println("- max capacity = " + maxCapacity);
        System.out.println("- number of empty entries = " + emptyEntries(table));
        if (isClassInvariantViolated) {
            System.out.println("- class invariant is violated!!! Violated clauses are:");
            printViolatedInvariantClauses(map, table);
        } else {
            System.out.println("- class invariant holds");
        }
    }

    // Counts the empty entries (the ones containing a null-key) in a table.
    private int emptyEntries(Object[] table)
            throws NoSuchFieldException, IllegalAccessException {
        int count = 0;
        for (int i = 0; i < table.length; i += 2) {
            if (table[i] == null) count++;
        }
        return count;
    }

    // Checks the invariant clauses for a map, and prints all violated ones.
    private void printViolatedInvariantClauses(IdentityHashMap<Object, Object> map, Object[] table)
            throws NoSuchFieldException, IllegalAccessException {
        final int maxCapacity = (int) getValueByStaticFieldName(IdentityHashMap.class, "MAXIMUM_CAPACITY");
        final int minCapacity = (int) getValueByStaticFieldName(IdentityHashMap.class, "MINIMUM_CAPACITY");
        final int threshold = (int) getValueByFieldName(map, "threshold");

        // Class invariant for IdentityHashMap:
        //    table != null &&
        //    MINIMUM_CAPACITY * 2 <= table.length &&
        //    MAXIMUM_CAPACITY * 2 >= table.length
        if (table == null)
            System.out.println("\t- table != null");
        if (table.length < minCapacity * 2)
            System.out.println("\t- MINIMUM_CAPACITY * 2 <= table.length");
        if (table.length > maxCapacity * 2)
            System.out.println("\t- MAXIMUM_CAPACITY * 2 >= table.length");

        // Class invariant for IdentityHashMap:
        //    (\forall int i;
        //        0 <= i && i < table.length - 1;
        //        i % 2 == 0 ==> (table[i] == null ==> table[i + 1] == null));
        // If the key is null, than the value must also be null
        for (int i = 0; i < table.length - 1; i += 2) {
            if (table[i] == null && table[i + 1] != null)
                System.out.println("\t- if the key is null, than the value must also be null");
        }

        // Class invariant for IdentityHashMap:
        //    (\forall int i; 0 <= i && i < table.length / 2;
        //       (\forall int j;
        //         i <= j && j < table.length / 2;
        //        (table[2*i] != null && table[2*i] == table[2*j]) ==> i == j));
        // Every none-null key is unique
        for (int i = 0; i < table.length / 2; i++) {
            if (table[2 * i] == null) continue; // Performance+
            for (int j = i; j < table.length / 2; j++) {
                if (table[2 * i] != null && table[2 * i] == table[2 * j]) {
                    if (i != j)
                        System.out.println("\t- every none-null key must be unique");
                }
            }
        }

        // Class invariant for IdentityHashMap:
        //     size == (\num_of int i;
        //        0 <= i < table.length /2;
        //        table[2*i] != null)
        // Size equals number of none-null keys in table
        int expectedSize = 0;
        for (int i = 0; i < table.length / 2; i++) {
            if (table[2 * i] != null) {
                expectedSize++;
            }
        }
        if (map.size() != expectedSize)
            System.out.println("\t- size must equal the number of none-null keys in table");

        // Class invariant for IdentityHashMap
        //   (\exists int i;
        //     0 <= i < table.length;
        //        \dl_pow(2,i) == table.length);
        // Table length is a power of two
        if (!((table.length & -table.length) == table.length))
            System.out.println("\t- table.length must be a power of two");

        // Class invariant for IdentityHashMap
        //   (\exists int i;
        //     0 <= i < table.length / 2;
        //     table[2*i] == null);
        // Table must have at least one empty key-element to prevent
        // infinite loops when a key is not present.
        boolean hasEmptyKey = false;
        for (int i = 0; i < table.length / 2; i++) {
            if (table[2 * i] == null) {
                hasEmptyKey = true;
                break;
            }
        }
        if (!hasEmptyKey)
            System.out.println("\t- table must have at least one empty key-element to prevent infinite loops when a key is not present");

        // Class invariant for IdentityHashMap
        //   (\forall int i;
        //     0 <= i < table.length / 2;
        //       table[2*i] != null && 2*i > hash(table[2*i], table.length) ==>
        //       (\forall int j;
        //         hash(table[2*i], table.length) <= 2*j < 2*i;
        //         table[2*j] != null));
        // There are no gaps between a key's hashed index and its actual
        // index (if the key is at a higher index than the hash code)
        for (int i = 0; i < table.length / 2; i++) {
            final int hash = hash(table[2 * i], table.length);
            if (table[2 * i] != null && 2 * i > hash) {
                for (int j = hash / 2; j < i; j++) {
                    if (!(table[2 * j] != null))
                        System.out.println("\t- there are no gaps between a key's hashed index and its actual index (if the key is at a higher index than the hash code)");
                }
            }
        }

        // Class invariant for IdentityHashMap
        //   (\forall int i;
        //     0 <= i < table.length / 2;
        //     table[2*i] != null && 2*i < hash(table[2*i], table.length) ==>
        //     (\forall int j;
        //       hash(table[2*i], table.length) <= 2*j < table.length || 0 <= 2*j < 2*i;
        //       table[2*j] != null));
        // There are no gaps between a key's hashed index and its actual
        // index (if the key is at a lower index than the hash code)
        for (int i = 0; i < table.length / 2; i++) {
            final int hash = hash(table[2 * i], table.length);
            if (table[2 * i] != null && 2 * i < hash) {
                for (int j = hash / 2; j < table.length / 2; j++) {
                    if (table[2 * j] == null)
                        System.out.println("\t- there are no gaps between a key's hashed index and its actual index (if the key is at a lower index than the hash code)");
                }
                for (int j = 0; j < i; j++) {
                    if (table[2 * j] == null)
                        System.out.println("\t- there are no gaps between a key's hashed index and its actual index (if the key is at a lower index than the hash code)");
                }
            }
        }

        // Class invariant  for IdentityHashMap
        //   size <= threshold &&
        //   size == threshold ==> size == MAXIMUM_CAPACITY - 1;
        // Bounds on size in relation to threshold
        if (map.size() > threshold)
            System.out.println("\t- size <= threshold");
        if (map.size() == threshold) {
            if (map.size() != (maxCapacity - 1))
                System.out.println("\t- size == threshold ==> size == MAXIMUM_CAPACITY - 1");
        }

        // Class invariant  for IdentityHashMap
        //   (threshold == table.length / 3 || threshold == MAXIMUM_CAPACITY - 1) &&
        //   table.length < 2 * MAXIMUM_CAPACITY ==> threshold == table.length / 3;
        // Bounds on threshold in relation to table.length and MAXIMUM_CAPACITY
        if (!(threshold == table.length / 3 || threshold == maxCapacity - 1))
            System.out.println("\t- bounds on threshold in relation to table.length and MAXIMUM_CAPACITY");
        if (table.length < maxCapacity * 2) {
            if (!(threshold == (table.length / 3)))
                System.out.println("\t- bounds on threshold in relation to table.length and MAXIMUM_CAPACITY");
        }
    }

}
