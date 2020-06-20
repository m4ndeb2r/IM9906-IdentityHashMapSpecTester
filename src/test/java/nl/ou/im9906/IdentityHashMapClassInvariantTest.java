package nl.ou.im9906;

import org.junit.Before;
import org.junit.Test;

import java.util.ArrayList;
import java.util.Collection;
import java.util.IdentityHashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map.Entry;
import java.util.Set;

import static nl.ou.im9906.TestHelper.getValueByFieldName;
import static nl.ou.im9906.TestHelper.isPowerOfTwo;
import static nl.ou.im9906.TestHelper.setValueByFieldName;
import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.Matchers.greaterThanOrEqualTo;
import static org.hamcrest.Matchers.lessThan;
import static org.hamcrest.Matchers.lessThanOrEqualTo;
import static org.hamcrest.Matchers.not;
import static org.hamcrest.Matchers.notNullValue;
import static org.hamcrest.core.Is.is;
import static org.junit.Assert.fail;

/**
 * This test class tests some of the JML specs added to the {@link IdentityHashMap}
 * in the 'IM9906 VerifiyingIdentityHashMap' project that aims to formally specify
 * that class.
 * <p>
 * For example, in this test class we play around with the {@link IdentityHashMap}
 * of the JDK7 (the version of the class under analysis), and with each step we check
 * if the class invariant(s) of the class and its inner classes still hold. This way
 * we can perform some preliminary sanity checks on these invariants to see if they
 * themselves are okay. (If one of the tests fails, there is, in theory, a chance that
 * the {@link IdentityHashMap} contains a bug, but it is more likely that the JML
 * specs (or the representation in this test class) contain an error.)
 */
public class IdentityHashMapClassInvariantTest {

    // Set this constant to true for extra output
    private static final boolean VERBOSE = true;

    // The test subject
    private IdentityHashMap<Object, Object> map;

    @Before
    public void setUp() {
        map = new IdentityHashMap<>();
    }

    /**
     * Tests of the class invariants hold after invocation of the several constructors
     * of the {@link IdentityHashMap}.
     *
     * @throws NoSuchFieldException   if any of the expected private fields does not exist
     * @throws IllegalAccessException if it was not possible to get acces to a required private field
     * @throws NoSuchClassException   if any of the expected inner classes does not exist
     */
    @Test
    public void testClassInvariantsAfterConstructorInvocation()
            throws NoSuchFieldException, IllegalAccessException, NoSuchClassException {
        assertClassInvariants(map);

        map = new IdentityHashMap<>(1 << 20);
        assertClassInvariants(map);
        map.values();
        map.keySet();
        map.entrySet();
        assertClassInvariants(map);

        map = new IdentityHashMap<>(0);
        assertClassInvariants(map);
        map.values();
        map.keySet();
        map.entrySet();
        assertClassInvariants(map);

        map = new IdentityHashMap<>(map);
        assertClassInvariants(map);
        try {
            map = new IdentityHashMap<>((IdentityHashMap<?, ?>) null);
            fail("Expected NullPointerException");
        } catch (NullPointerException e) {
            // Ok. Expected.
        }
    }

    /**
     * Tests is the class invariants hold after adding and removing elements
     * to the {@link IdentityHashMap}, and cloning an cleaning it.
     *
     * @throws NoSuchFieldException   if any of the expected private fields does not exist
     * @throws IllegalAccessException if it was not possible to get acces to a required private field
     * @throws NoSuchClassException   if any of the expected inner classes does not exist
     */
    @Test
    public void testClassInvariantsAfterPutRemoveClearClone()
            throws NoSuchFieldException, IllegalAccessException, NoSuchClassException {
        assertClassInvariants(map);

        final List<String> keys = new ArrayList<>();
        for (int i = 0; i < 2000; i++) {
            keys.add("key" + i);
        }

        // Add some entries
        for (String key : keys) map.put(key, "someValue");
        Set<Object> keySet = map.keySet();
        Collection<Object> values = map.values();
        Set<Entry<Object, Object>> entries = map.entrySet();
        assertThat(map.size(), is(keys.size()));
        assertThat(entries.size(), is(map.size()));
        assertThat(keySet.size(), is(map.size()));
        assertThat(values.size(), is(map.size()));
        assertClassInvariants(map);

        // Overwrite values of existing entries
        for (String key : keys) map.put(key, "someOtherValue");
        keySet = map.keySet();
        values = map.values();
        entries = map.entrySet();
        assertThat(map.size(), is(keys.size()));
        assertThat(entries.size(), is(map.size()));
        assertThat(keySet.size(), is(map.size()));
        assertThat(values.size(), is(map.size()));
        assertClassInvariants(map);

        // Clone the map
        final IdentityHashMap<Object, Object> clone = (IdentityHashMap<Object, Object>) map.clone();

        // Remove all elements from the original map
        for (String key : keys) map.remove(key);
        assertThat(map.size(), is(0));
        assertThat(entries.size(), is(map.size()));
        assertThat(keySet.size(), is(map.size()));
        assertThat(values.size(), is(map.size()));
        assertClassInvariants(map);

        // Check is the clone is still untouched
        keySet = clone.keySet();
        values = clone.values();
        entries = clone.entrySet();
        assertThat(clone.size(), is(keys.size()));
        assertThat(entries.size(), is(clone.size()));
        assertThat(keySet.size(), is(clone.size()));
        assertThat(values.size(), is(clone.size()));
        assertClassInvariants(clone);

        // Clean the clone
        clone.clear();
        assertThat(clone.size(), is(0));
        assertThat(entries.size(), is(0));
        assertThat(keySet.size(), is(0));
        assertThat(values.size(), is(0));
        assertClassInvariants(clone);
    }

    /**
     * A test with nested {@link IdentityHashMap}s, to see if the class invariants
     * still hold after several operations on the maps.
     *
     * @throws NoSuchFieldException   if any of the expected private fields does not exist
     * @throws IllegalAccessException if it was not possible to get acces to a required private field
     * @throws NoSuchClassException   if any of the expected inner classes does not exist
     */
    @Test
    public void testClassInvariantsForRecursiveIdentityHashMap()
            throws NoSuchFieldException, IllegalAccessException, NoSuchClassException {
        assertClassInvariants(map);

        final Set<Entry<Object, Object>> entries = map.entrySet();
        final Set<Object> keySet = map.keySet();
        final Collection<Object> values = map.values();
        assertClassInvariants(map);

        for (int i = 0; i < 2000; i++) {
            map.put(map.clone(), entries);
            assertClassInvariants(map);
        }
        assertThat(map.size(), is(2000));
        assertThat(entries.size(), is(map.size()));
        assertThat(keySet.size(), is(map.size()));
        assertThat(values.size(), is(map.size()));
        map.putAll(map);
        assertThat(map.size(), is(2000));
        assertThat(entries.size(), is(map.size()));
        assertThat(keySet.size(), is(map.size()));
        assertThat(values.size(), is(map.size()));
        assertClassInvariants(map);

        while (map.size() > 1000) {
            map.remove(map.keySet().toArray()[map.size() - 1]);
            assertClassInvariants(map);
        }
        assertThat(map.size(), is(1000));
        assertThat(entries.size(), is(map.size()));
        assertThat(keySet.size(), is(map.size()));
        assertThat(values.size(), is(map.size()));
        assertClassInvariants(map);

        map.clear();
        assertThat(map.size(), is(0));
        assertThat(entries.size(), is(map.size()));
        assertThat(keySet.size(), is(map.size()));
        assertThat(values.size(), is(map.size()));
        assertClassInvariants(map);
    }

    /**
     * Tests if the class invariants still hold after the modCount field overflows
     * (which will happen after too many modifications of the {@link IdentityHashMap},
     * but should not cause any real errors). The modCount field is set to a large
     * number (Integer.MAX_VALUE - 1) using reflection. After that, some testing is
     * done by modifying the map.
     *
     * @throws NoSuchFieldException   if any of the expected private fields does not exist
     * @throws IllegalAccessException if it was not possible to get acces to a required private field
     * @throws NoSuchClassException   if any of the expected inner classes does not exist
     */
    @Test
    public void testClassInvariantsWithLargeModCountInIdentityHashMap()
            throws NoSuchFieldException, IllegalAccessException, NoSuchClassException {
        setValueByFieldName((IdentityHashMap<?, ?>) map, "modCount", Integer.MAX_VALUE - 1);
        for (int i = 0; i < 3; i++) {
            map.put("key" + i, "val" + i);
            assertClassInvariants(map);
        }
        map.clear();
        assertClassInvariants(map);
    }

    /**
     * Checks the class invariants of the main class as well as the inner classes.
     *
     * @param map an instance of the {@link IdentityHashMap}
     * @throws NoSuchFieldException   if any of the expected private fields does not exist
     * @throws IllegalAccessException if it was not possible to get acces to a required private field
     * @throws NoSuchClassException   if any of the expected inner classes does not exist
     */
    private void assertClassInvariants(IdentityHashMap<?, ?> map)
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
    private void assertIdentityHashMapClassInvariant(IdentityHashMap<?, ?> map)
            throws NoSuchFieldException, IllegalAccessException {
        final int minimumCapacity = (int) getValueByFieldName(map, "MINIMUM_CAPACITY");
        final int maximumCapacity = (int) getValueByFieldName(map, "MAXIMUM_CAPACITY");
        final Object[] table = (Object[]) getValueByFieldName(map, "table");

        // Class invariant for IdentityHashMap:
        //    table != null &&
        //    MINIMUM_CAPACITY == 4 && MAXIMUM_CAPACITY == 1 << 29 &&
        //    MINIMUM_CAPACITY <= table.length && table.length <= MAXIMUM_CAPACITY &&
        //    (table.length & (table.length - 1)) == 0
        // Table.length must be between 4 and 1 << 29 (constants MINIMUM_CAPACITY and MAXIMUM_CAPACITY respectively),
        // and must be a power of 2.
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
            if (table[j] == null) {
                assertThat(table[i] == null, is(true));
            }
        }

        // Class invariant for IdentityHashMap:
        //    (\forall int i;
        //        0 <= i < table.length - 1 && i % 2 == 0;
        //        table[i] != null &&
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
        try {
            final int threshold = (int) getValueByFieldName(map, "threshold");
            assertThat(threshold, greaterThanOrEqualTo(0));
            assertThat(threshold, lessThanOrEqualTo(Integer.MAX_VALUE));
            assertThat(threshold, is(table.length / 3));
        } catch (NoSuchFieldException e) {
            if (VERBOSE) {
                System.out.println("WARNING: Field threshold not present in IdentityHashMap of this Java version. Skipped.");
            }
        }

        // Class invariant for IdentityHashMap
        //    entrySet != null ==>
        //       (\forall Entry e;
        //           entrySet.contains(e);
        //           (\exists \bigint i;
        //                0 <= i < table.length - 1 && i % 2 == 0;
        //                table[i] == e.getKey() && table[i+1] == e.getValue()))
        final Set<Entry<?, ?>> entrySet = (Set<Entry<?, ?>>) getValueByFieldName(map, "entrySet");
        if (entrySet != null) {
            for (Entry<?, ?> e : entrySet) {
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
    private void assertIdentityHashMapIteratorClassInvariant(IdentityHashMap<?, ?> map)
            throws NoSuchFieldException, IllegalAccessException, NoSuchClassException {
        final Object[] table = (Object[]) getValueByFieldName(map, "table");
        final Collection<?> values = (Collection<?>) getValueByFieldName(map, "values");
        final Set<?> keySet = (Set<?>) getValueByFieldName(map, "keySet");
        final Set<Entry<?, ?>> entrySet = (Set<Entry<?, ?>>) getValueByFieldName(map, "entrySet");

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

    private void assertEntryIteratorClassInvariant(IdentityHashMap<?, ?> map)
            throws NoSuchClassException, NoSuchFieldException, IllegalAccessException {
        final Set<Entry<?, ?>> entrySet = (Set<Entry<?, ?>>) getValueByFieldName(map, "entrySet");

        // Class invariant for the EntryIterator inner class
        //    lastReturnedEntry != null ==> lastReturnedIndex == lastReturnedEntry.index &&
        //    lastReturnedEntry == null ==> lastReturnedIndex == -1
        if (entrySet != null) {
            final Entry<?, ?> lastReturnedEntry = (Entry<?, ?>) getValueByFieldName(entrySet.iterator(), "lastReturnedEntry");
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
    private void assertEntryClassInvariant(IdentityHashMap<?, ?> map)
            throws NoSuchFieldException, IllegalAccessException, NoSuchClassException {
        // Class invariant for the Entry inner class of the EntryIterator inner class
        //    0 <= index < traversalTable.length - 1
        // Check this for all entries in the entrySet field of the map
        final Set<Entry<?, ?>> entrySet = (Set<Entry<?, ?>>) getValueByFieldName(map, "entrySet");
        if (entrySet != null) {
            final Iterator<Entry<?, ?>> entryIterator = entrySet.iterator();
            final Object[] traversalTable = (Object[]) getValueByFieldName(entryIterator, "traversalTable");
            while (entryIterator.hasNext()) {
                final int index = (int) getValueByFieldName(entryIterator.next(), "index");
                assertThat(index, greaterThanOrEqualTo(0));
                assertThat(index, lessThan(traversalTable.length - 1));
            }
        }
    }

}
