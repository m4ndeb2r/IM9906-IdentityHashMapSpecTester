package nl.ou.im9906;

import java.util.Collection;
import java.util.IdentityHashMap;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;

import static nl.ou.im9906.ReflectionUtils.getValueByFieldName;
import static nl.ou.im9906.ReflectionUtils.isPowerOfTwo;
import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.Matchers.greaterThanOrEqualTo;
import static org.hamcrest.Matchers.lessThan;
import static org.hamcrest.Matchers.lessThanOrEqualTo;
import static org.hamcrest.Matchers.not;
import static org.hamcrest.Matchers.notNullValue;
import static org.hamcrest.core.Is.is;

public class ClassInvariantTestHelper {

    /**
     * Checks the class invariants of the main class as well as the inner classes.
     *
     * @param map an instance of the {@link IdentityHashMap}
     * @throws NoSuchFieldException   if any of the expected private fields does not exist
     * @throws IllegalAccessException if it was not possible to get acces to a required private field
     * @throws NoSuchClassException   if any of the expected inner classes does not exist
     */
    protected static void assertClassInvariants(IdentityHashMap<?, ?> map)
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
     * @throws IllegalAccessException if it was not possible to get acces to a required private field
     */
    private static void assertIdentityHashMapClassInvariant(IdentityHashMap<?, ?> map)
            throws NoSuchFieldException, IllegalAccessException {
        final int minimumCapacity = (int) getValueByFieldName(map, "MINIMUM_CAPACITY");
        final int maximumCapacity = (int) getValueByFieldName(map, "MAXIMUM_CAPACITY");
        final Object[] table = (Object[]) getValueByFieldName(map, "table");

        // Class invariant for IdentityHashMap:
        //    table != null &&
        //    MINIMUM_CAPACITY == 4 && MAXIMUM_CAPACITY == 536870912 &&
        //    MINIMUM_CAPACITY <= table.length && table.length <= MAXIMUM_CAPACITY &&
        //    (\exists \bigint i;
        //        0 <= i < table.length;
        //        \dl_pow(2,i) == table.length)
        // Table.length must be between 4 and 536870912 (constants MINIMUM_CAPACITY and MAXIMUM_CAPACITY
        // respectively), and must be a power of 2.
        assertThat(table, notNullValue());
        assertThat(table.length, greaterThanOrEqualTo(minimumCapacity));
        assertThat(table.length, lessThanOrEqualTo(maximumCapacity));
        assertThat(isPowerOfTwo(table.length), is(true));

        // Class invariant for IdentityHashMap:
        //    (\forall int i, j;
        //        0 <= i && j == i + 1 && j < table.length;
        //        table[i] == null ==> table[j] == null)
        // If the key is null, than the value must also be null
        for (int i = 0; i < table.length - 1; i += 2) {
            final int j = i + 1;
            if (table[i] == null) {
                assertThat(table[j] == null, is(true));
            }
        }

        // Class invariant for IdentityHashMap:
        //    (\forall int i, j;
        //        0 <= i && j == i + 1 && j < table.length;
        //        table[j] != null ==> table[i] != null)
        // If the value is not null, then the key must also not be null
        for (int i = 0; i < table.length - 1; i += 2) {
            final int j = i + 1;
            if (table[j] != null) {
                assertThat(table[i] != null, is(true));
            }
        }

        // Class invariant for IdentityHashMap:
        //    (\forall int i;
        //        0 <= i < table.length - 1 && i % 2 == 0;
        //        table[i] != null ==>
        //        !(\exists int j;
        //            i + 2 <= j < table.length - 1 && j % 2 == 0;
        //            table[i] == table[j]))
        // Every none-null key is unique
        for (int i = 0; i < table.length - 1; i += 2) {
            if (table[i] != null) {
                for (int j = i + 2; j < table.length - 1; j += 2) {
                    assertThat(table[i], not(table[j]));
                }
            }
        }

        // Class invariant for IdentityHashMap:
        //     size >= 0 &&
        //     size <= (table.length / 2) &&
        //     size == (\num_of int i;
        //        0 <= i < table.length - 1 && i % 2 == 0;
        //        table[i] != null)
        // Size > 0, size <= table.length, and size equals number of none-null keys in table
        assertThat(map.size(), greaterThanOrEqualTo(0));
        assertThat(map.size(), lessThanOrEqualTo(table.length / 2));
        int expectedSize = 0;
        for (int i = 0; i < table.length; i += 2) {
            if (table[i] != null) {
                expectedSize++;
            }
        }
        assertThat(map.size(), is(expectedSize));

        // Class invariant for IdentityHashMap:
        //     threshold >= 0 &&
        //     threshold <= Integer.MAX_VALUE &&
        //     threshold == table.length / 3
        // Note: in newer JDK-versions (8+) this field does no longer exist
        final int threshold = (int) getValueByFieldName(map, "threshold");
        assertThat(threshold, greaterThanOrEqualTo(0));
        assertThat(threshold, lessThanOrEqualTo(Integer.MAX_VALUE));
        assertThat(threshold, is(table.length / 3));

        // Class invariant for IdentityHashMap
        //    entrySet != null ==>
        //       (\forall Entry e;
        //           entrySet.contains(e);
        //           (\exists \bigint i;
        //                0 <= i < table.length - 1 && i % 2 == 0;
        //                table[i] == e.getKey() && table[i+1] == e.getValue()))
        final Set<Map.Entry<?, ?>> entrySet = (Set<Map.Entry<?, ?>>) getValueByFieldName(map, "entrySet");
        if (entrySet != null) {
            for (Map.Entry<?, ?> e : entrySet) {
                boolean found = false;
                for (int i = 0; i < table.length - 1; i += 2) {
                    if (table[i] == e.getKey() && table[i + 1] == e.getValue()) {
                        found = true;
                        break;
                    }
                }
                assertThat(found, is(true));
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
    private static void assertIdentityHashMapIteratorClassInvariant(IdentityHashMap<?, ?> map)
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

    private static void assertEntryIteratorClassInvariant(IdentityHashMap<?, ?> map)
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
    private static void assertEntryClassInvariant(IdentityHashMap<?, ?> map)
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
