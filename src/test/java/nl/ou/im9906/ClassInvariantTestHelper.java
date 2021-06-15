package nl.ou.im9906;

import java.util.AbstractMap;
import java.util.Collection;
import java.util.IdentityHashMap;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;

import static nl.ou.im9906.ReflectionUtils.getValueByFieldName;
import static nl.ou.im9906.ReflectionUtils.hash;
import static nl.ou.im9906.ReflectionUtils.isPowerOfTwo;
import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.Matchers.greaterThanOrEqualTo;
import static org.hamcrest.Matchers.lessThan;
import static org.hamcrest.Matchers.lessThanOrEqualTo;
import static org.hamcrest.Matchers.notNullValue;
import static org.hamcrest.core.Is.is;

/**
 * A helper/utility class containing helper methods for testing the class
 * invariant of the {@link IdentityHashMap}.
 */
public class ClassInvariantTestHelper {

    private static final boolean VERBOSE = false;

    /**
     * Checks the class invariants of the main class as well as the inner classes.
     *
     * @param map an instance of the {@link IdentityHashMap}
     * @throws NoSuchFieldException   if any of the expected private fields does not exist
     * @throws IllegalAccessException if it was not possible to get access to a required private field
     * @throws NoSuchClassException   if any of the expected inner classes does not exist
     */
    protected static void assertClassInvariants(AbstractMap<?, ?> map)
            throws NoSuchFieldException, IllegalAccessException, NoSuchClassException {
        // Assert invariant checks on the IdentityHashMap level
        assertIdentityHashMapClassInvariant(map);
        // Assert invariant checks on the IdentityHashMap$IdentityHashMapIterator level
        assertIdentityHashMapIteratorClassInvariant(map);
        // Assert invariant checks on the IdentityHashMap$EntryIterator level
        assertEntryIteratorClassInvariant(map);
        // Assert invariant checks on the IdentityHashMap$Entry level
        assertEntryClassInvariant(map);
    }

    /**
     * Checks the class invariant of the main class ({@link IdentityHashMap}).
     *
     * @param map an instance of the {@link IdentityHashMap} to test
     * @throws NoSuchFieldException   if any of the expected private fields does not exist
     * @throws IllegalAccessException if it was not possible to get access to a required private field
     */
    private static void assertIdentityHashMapClassInvariant(AbstractMap<?, ?> map)
            throws NoSuchFieldException, IllegalAccessException {
        final int minimumCapacity = (int) getValueByFieldName(map, "MINIMUM_CAPACITY");
        final int maximumCapacity = (int) getValueByFieldName(map, "MAXIMUM_CAPACITY");
        final Object[] table = (Object[]) getValueByFieldName(map, "table");

        // Class invariant for IdentityHashMap:
        //    table != null &&
        //    MINIMUM_CAPACITY == 4 &&
        //    MAXIMUM_CAPACITY == 536870912 &&
        //    MINIMUM_CAPACITY * 2 <= table.length &&
        //    MAXIMUM_CAPACITY * 2 >= table.length
        // Table.length must be between 4 * 2 and 536870912 * 2 (constants MINIMUM_CAPACITY * 2
        // and MAXIMUM_CAPACITY * 2 respectively).
        assertThat(table, notNullValue());
        assertThat(table.length, greaterThanOrEqualTo(minimumCapacity * 2));
        assertThat(table.length, lessThanOrEqualTo(maximumCapacity * 2));

        // Class invariant for IdentityHashMap:
        //    (\forall int i;
        //        0 <= i && i < table.length - 1;
        //        i % 2 == 0 ==> (table[i] == null ==> table[i + 1] == null));
        // If the key is null, than the value must also be null
        for (int i = 0; i < table.length - 1; i += 2) {
            if (table[i] == null) {
                assertThat(table[i + 1] == null, is(true));
            }
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
                    assertThat(i, is(j));
                }
            }
        }

        // Class invariant for IdentityHashMap:
        //    threshold < MAXIMUM_CAPACITY
        final int threshold = (int) getValueByFieldName(map, "threshold");
        assertThat(threshold, lessThan(maximumCapacity));

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
        assertThat(map.size(), is(expectedSize));

        // Class invariant for IdentityHashMap
        //   (\exists int i;
        //     0 <= i < table.length;
        //        \dl_pow(2,i) == table.length);
        // Table length is a power of two
        assertThat(isPowerOfTwo(table.length), is(true));

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
        assertThat(hasEmptyKey, is(true));

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
                    assertThat(table[2 * j] != null, is(true));
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
                if (VERBOSE) {
                    System.out.println(String.format("Actual index = %d. Hash = %d. Length of table = %d", 2 * i, hash, table.length));
                    System.out.println(String.format("Checking if table element %d to %d are <> null", hash, 2 * i));
                }

                for (int j = hash / 2; j < table.length / 2; j++) {
                    final String msg = String.format("Value (key) in table[%d] was not expected to be null.", 2 * j);
                    if (VERBOSE) System.out.println(String.format("Checking element %d", 2 * j));
                    assertThat(msg, table[2 * j] != null, is(true));
                }
                for (int j = 0; j < i; j++) {
                    final String msg = String.format("Key in table[%d] was not expected to be null.", 2 * j);
                    if (VERBOSE) {
                        System.out.println(String.format("Checking element %d", 2 * j));
                        if (table[2 * j] == null) {
                            System.out.println("\nERROR: " + msg);
                            for (int k = Math.max(0, 2 * j - 10); k < 2 * j + 10; k += 2) {
                                System.out.println(String.format("Index %d: <%s, %s>; newly calculated hash: %d",
                                        k % table.length,
                                        table[k % table.length],
                                        table[k % table.length + 1],
                                        hash(table[k], table.length)));
                            }
                        }
                    }
                    assertThat(msg, table[2 * j] != null, is(true));
                }
            }
        }
    }

    /**
     * Checks the class invariant of the inner class IdentityHashMap#IdentityHashMapIterator.
     *
     * @param map an instance of the {@link IdentityHashMap} to test
     * @throws NoSuchFieldException
     * @throws IllegalAccessException
     * @throws NoSuchClassException
     */
    private static void assertIdentityHashMapIteratorClassInvariant(AbstractMap<?, ?> map)
            throws NoSuchFieldException, IllegalAccessException, NoSuchClassException {
        final Object[] table = (Object[]) getValueByFieldName(map, "table");
        final Collection<?> values = (Collection<?>) getValueByFieldName(map, "values");
        final Set<?> keySet = (Set<?>) getValueByFieldName(map, "keySet");
        final Set<Map.Entry<?, ?>> entrySet = (Set<Map.Entry<?, ?>>) getValueByFieldName(map, "entrySet");

        // Class invariant for IdentityHashMapIterator inner class (and subclasses)
        //    0 <= index <= table.length
        if (values != null) {
            final Integer valIndex = (Integer) getValueByFieldName(values.iterator(), "index");
            assertThat(valIndex, greaterThanOrEqualTo(0));
            assertThat(valIndex, lessThanOrEqualTo(table.length));
        }
        if (keySet != null) {
            Iterator<?> keyIterator = keySet.iterator();
            final Integer keyIndex = (Integer) getValueByFieldName(keyIterator, "index");
            assertThat(keyIndex, greaterThanOrEqualTo(0));
            assertThat(keyIndex, lessThanOrEqualTo(table.length));
        }
        if (entrySet != null) {
            final Integer entryIndex = (Integer) getValueByFieldName(entrySet.iterator(), "index");
            assertThat(entryIndex, greaterThanOrEqualTo(0));
            assertThat(entryIndex, is(lessThanOrEqualTo(table.length)));
        }

        // Class invariant for IdentityHashMapIterator inner class (and subclasses)
        //    -1 <= lastReturnedIndex <= table.length
        if (values != null) {
            final int lastReturnedValIndex = (int) getValueByFieldName(values.iterator(), "lastReturnedIndex");
            assertThat(lastReturnedValIndex, greaterThanOrEqualTo(-1));
            assertThat(lastReturnedValIndex, lessThanOrEqualTo(table.length));
        }
        if (keySet != null) {
            final int lastReturnedKeyIndex = (int) getValueByFieldName(keySet.iterator(), "lastReturnedIndex");
            assertThat(lastReturnedKeyIndex, greaterThanOrEqualTo(-1));
            assertThat(lastReturnedKeyIndex, lessThanOrEqualTo(table.length));
        }
        if (entrySet != null) {
            final int lastReturnedEntryIndex = (int) getValueByFieldName(entrySet.iterator(), "lastReturnedIndex");
            assertThat(lastReturnedEntryIndex, greaterThanOrEqualTo(-1));
            assertThat(lastReturnedEntryIndex, lessThanOrEqualTo(table.length));
        }

        // Class invariant for IdentityHashMapIterator inner class (and subclasses)
        //    traversableTable.length == table.length &&
        //    (\forall \bigint i;
        //        0 <= i && i < table.length;
        //       table[i] == traversableTable[i])
        // Any element in table must be present in traversableTable and vice versa
        if (values != null) {
            final Object[] traversalTable = (Object[]) getValueByFieldName(values.iterator(), "traversalTable");
            assertThat(traversalTable.length, is(table.length));
            for (int i = 0; i < traversalTable.length; i++) {
                assertThat(traversalTable[i] == table[i], is(true));
            }
        }
        if (keySet != null) {
            final Object[] traversalTable = (Object[]) getValueByFieldName(keySet.iterator(), "traversalTable");
            assertThat(traversalTable.length, is(table.length));
            for (int i = 0; i < traversalTable.length; i++) {
                assertThat(traversalTable[i] == table[i], is(true));
            }
        }
        if (entrySet != null) {
            final Object[] traversalTable = (Object[]) getValueByFieldName(entrySet.iterator(), "traversalTable");
            assertThat(traversalTable.length, is(table.length));
            for (int i = 0; i < traversalTable.length; i++) {
                assertThat(traversalTable[i] == table[i], is(true));
            }
        }
    }

    private static void assertEntryIteratorClassInvariant(AbstractMap<?, ?> map)
            throws NoSuchClassException, NoSuchFieldException, IllegalAccessException {
        final Set<Map.Entry<?, ?>> entrySet = (Set<Map.Entry<?, ?>>) getValueByFieldName(map, "entrySet");

        // Class invariant for the EntryIterator inner class
        //    lastReturnedEntry != null ==> lastReturnedIndex == lastReturnedEntry.index &&
        //    lastReturnedEntry == null ==> lastReturnedIndex == -1
        if (entrySet != null) {
            final Map.Entry<?, ?> lastReturnedEntry = (Map.Entry<?, ?>) getValueByFieldName(entrySet.iterator(), "lastReturnedEntry");
            final int lastReturnedIndex = (int) getValueByFieldName(entrySet.iterator(), "lastReturnedIndex");
            if (lastReturnedEntry != null) {
                final int lastReturnedEntryIndex = (int) getValueByFieldName(lastReturnedEntry, "index");
                assertThat(lastReturnedEntryIndex, is(lastReturnedIndex));
            } else {
                assertThat(lastReturnedIndex, is(-1));
            }
        }
    }

    /**
     * Checks the class invariant of the inner class IdentityHashMap#EntryIterator#Entry.
     *
     * @param map an instance of the {@link IdentityHashMap} to test
     * @throws NoSuchFieldException
     * @throws IllegalAccessException
     * @throws NoSuchClassException
     */
    private static void assertEntryClassInvariant(AbstractMap<?, ?> map)
            throws NoSuchFieldException, IllegalAccessException, NoSuchClassException {
        // Class invariant for the Entry inner class of the EntryIterator inner class
        //    0 <= index < traversalTable.length - 1
        // Check this for all entries in the entrySet field of the map
        final Set<Map.Entry<?, ?>> entrySet = (Set<Map.Entry<?, ?>>) getValueByFieldName(map, "entrySet");
        if (entrySet != null) {
            final Iterator<Map.Entry<?, ?>> entryIterator = entrySet.iterator();
            final Object[] traversalTable = (Object[]) getValueByFieldName(entryIterator, "traversalTable");
            while (entryIterator.hasNext()) {
                final int index = (int) getValueByFieldName(entryIterator.next(), "index");
                assertThat(index, greaterThanOrEqualTo(0));
                assertThat(index, lessThan(traversalTable.length - 1));
            }
        }
    }

}
