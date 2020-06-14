package nl.ou.im9906;

import org.junit.Before;
import org.junit.Test;

import java.lang.reflect.Field;
import java.util.AbstractMap;
import java.util.ArrayList;
import java.util.Collection;
import java.util.IdentityHashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map.Entry;
import java.util.Set;

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
        setIntegerFieldByName(map, "modCount", Integer.MAX_VALUE - 1);
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
        final int minimumCapacity = getIntegerFieldByName(map, "MINIMUM_CAPACITY");
        final int maximumCapacity = getIntegerFieldByName(map, "MAXIMUM_CAPACITY");
        final Object[] table = getTable(map);

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
            final int threshold = getIntegerFieldByName(map, "threshold");
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
        final Set<Entry<?, ?>> entrySet = getEntrySet(map);
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
        final Object[] table = getTable(map);
        final Collection<?> values = getValues(map);
        final Set<?> keySet = getKeySet(map);
        final Set<Entry<?, ?>> entrySet = getEntrySet(map);

        // Class invariant for IdentityHashMapIterator inner class (and subclasses)
        //    0 <= index <= table.length
        if (values != null) {
            final Integer valIndex = getIntegerFieldByNameFromValueIterator(values.iterator(), "index");
            assertThat(valIndex, greaterThanOrEqualTo(0));
            assertThat(valIndex, lessThanOrEqualTo(table.length));
        }
        if (keySet != null) {
            final Integer keyIndex = getIntegerFieldByNameFromKeyIterator(keySet.iterator(), "index");
            assertThat(keyIndex, greaterThanOrEqualTo(0));
            assertThat(keyIndex, lessThanOrEqualTo(table.length));
        }
        if (entrySet != null) {
            final Integer entryIndex = getIntegerFieldByNameFromEntryIterator(entrySet.iterator(), "index");
            assertThat(entryIndex, greaterThanOrEqualTo(0));
            assertThat(entryIndex, is(lessThanOrEqualTo(table.length)));
        }

        // Class invariant for IdentityHashMapIterator inner class (and subclasses)
        //    -1 <= lastReturnedIndex <= table.length
        if (values != null) {
            final Integer lastReturnedValIndex = getIntegerFieldByNameFromValueIterator(values.iterator(), "lastReturnedIndex");
            assertThat(lastReturnedValIndex, greaterThanOrEqualTo(-1));
            assertThat(lastReturnedValIndex, lessThanOrEqualTo(table.length));
        }
        if (keySet != null) {
            final Integer lastReturnedKeyIndex = getIntegerFieldByNameFromKeyIterator(keySet.iterator(), "lastReturnedIndex");
            assertThat(lastReturnedKeyIndex, greaterThanOrEqualTo(-1));
            assertThat(lastReturnedKeyIndex, lessThanOrEqualTo(table.length));
        }
        if (entrySet != null) {
            final Integer lastReturnedEntryIndex = getIntegerFieldByNameFromEntryIterator(entrySet.iterator(), "lastReturnedIndex");
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
            final Object[] traversalTable = getTraversalTableFromValueIterator(values.iterator());
            assertThat(traversalTable.length, is(table.length));
            for (int i = 0; i < traversalTable.length; i++) {
                assertThat(traversalTable[i] == table[i], is(true));
            }
        }
        if (keySet != null) {
            final Object[] traversalTable = getTraversalTableFromKeyIterator(keySet.iterator());
            assertThat(traversalTable.length, is(table.length));
            for (int i = 0; i < traversalTable.length; i++) {
                assertThat(traversalTable[i] == table[i], is(true));
            }
        }
        if (entrySet != null) {
            final Object[] traversalTable = getTraversalTableFromEntryIterator(entrySet.iterator());
            assertThat(traversalTable.length, is(table.length));
            for (int i = 0; i < traversalTable.length; i++) {
                assertThat(traversalTable[i] == table[i], is(true));
            }
        }
    }

    private void assertEntryIteratorClassInvariant(IdentityHashMap<?, ?> map)
            throws NoSuchClassException, NoSuchFieldException, IllegalAccessException {
        final Set<Entry<?, ?>> entrySet = getEntrySet(map);

        // Class invariant for the EntryIterator inner class
        //    lastReturnedEntry != null ==> lastReturnedIndex == lastReturnedEntry.index &&
        //    lastReturnedEntry == null ==> lastReturnedIndex == -1
        if (entrySet != null) {
            final Entry<?, ?> lastReturnedEntry = getLastReturnedEntryFromEntryIterator(entrySet.iterator());
            final Integer lastReturnedIndex = getIntegerFieldByNameFromEntryIterator(entrySet.iterator(), "lastReturnedIndex");
            if (lastReturnedEntry != null) {
                final Integer lastReturnedEntryIndex = getIntegerFieldByNameFromEntry(lastReturnedEntry, "index");
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
        final Set<Entry<?, ?>> entrySet = getEntrySet(map);
        if (entrySet != null) {
            final Iterator<Entry<?, ?>> entryIterator = entrySet.iterator();
            final Object[] traversalTable = getTraversalTableFromEntryIterator(entryIterator);
            while (entryIterator.hasNext()) {
                final Integer index = getIntegerFieldByNameFromEntry(entryIterator.next(), "index");
                assertThat(index, greaterThanOrEqualTo(0));
                assertThat(index, lessThan(traversalTable.length - 1));
            }
        }
    }

    /**
     * Get the value of the private field table from the specified map using
     * reflection.
     *
     * @param map an instance of the {@link IdentityHashMap}
     * @return the private table field
     * @throws NoSuchFieldException
     * @throws IllegalAccessException
     */
    private Object[] getTable(IdentityHashMap<?, ?> map)
            throws NoSuchFieldException, IllegalAccessException {
        final Field tableField = IdentityHashMap.class.getDeclaredField("table");
        tableField.setAccessible(true);
        return (Object[]) tableField.get(map);
    }

    /**
     * Get the value of integer field with the specified fieldName from the specified
     * map using reflection.
     *
     * @param map       an instance of the {@link IdentityHashMap}
     * @param fieldName the name of the private field to get (this must be a field of
     *                  type integer)
     * @return the value of requested field
     * @throws NoSuchFieldException
     * @throws IllegalAccessException
     */
    private int getIntegerFieldByName(IdentityHashMap<?, ?> map, String fieldName)
            throws NoSuchFieldException, IllegalAccessException {
        final Field field = IdentityHashMap.class.getDeclaredField(fieldName);
        field.setAccessible(true);
        return (Integer) field.get(map);
    }

    /**
     * Set the value of the integer field with the specified fieldName in the specified
     * map using reflection.
     *
     * @param map       an instance of the {@link IdentityHashMap}
     * @param fieldName the name of the field that is to be modified
     * @param value     the new value of the field
     * @throws NoSuchFieldException
     * @throws IllegalAccessException
     */
    private void setIntegerFieldByName(IdentityHashMap<?, ?> map, String fieldName, int value)
            throws NoSuchFieldException, IllegalAccessException {
        final Field field = IdentityHashMap.class.getDeclaredField(fieldName);
        field.setAccessible(true);
        field.set(map, value);
    }

    /**
     * Get the value of the field entrySet from the specified map using reflection.
     *
     * @param map an instance of the {@link IdentityHashMap}
     * @return the private entrySet field
     * @throws NoSuchFieldException
     * @throws IllegalAccessException
     */
    private Set<Entry<?, ?>> getEntrySet(IdentityHashMap<?, ?> map)
            throws NoSuchFieldException, IllegalAccessException {
        final Field entrySetField = IdentityHashMap.class.getDeclaredField("entrySet");
        entrySetField.setAccessible(true);
        return (Set<Entry<?, ?>>) entrySetField.get(map);
    }

    /**
     * Get the private integer field with the specified fieldName from the
     * IdentityHashMap$EntryIterator inner class, using reflection.
     *
     * @param entryIterator an instance of the IdentityHashMap$EntryIterator
     * @param fieldName     the name of the requested field
     * @return the value of the requested field
     * @throws NoSuchFieldException   if the request field does not exist
     * @throws IllegalAccessException if it was not possible to get access to the field
     * @throws NoSuchClassException   if the inner class EntryIterator does not exist
     */
    private Integer getIntegerFieldByNameFromEntryIterator(Iterator<Entry<?, ?>> entryIterator, String fieldName)
            throws NoSuchFieldException, IllegalAccessException, NoSuchClassException {
        final Class<?> entryIteratorClass = getInnerClass("EntryIterator");
        Field declaredField;
        try {
            declaredField = entryIteratorClass.getDeclaredField(fieldName);
        } catch (NoSuchFieldException e) {
            final Class<?> identityHashMapIteratorClass = entryIteratorClass.getSuperclass();
            declaredField = identityHashMapIteratorClass.getDeclaredField(fieldName);
        }
        declaredField.setAccessible(true);
        return (Integer) declaredField.get(entryIterator);
    }

    /**
     * Get the traversalTable field from the IdentityHashMap$EntryIterator inner class,
     * using reflection.
     *
     * @param entryIterator an instance of the IdentityHashMap$EntryIterator
     * @return the requested traversalTable field, or {@code null} if it is not instantiated
     * @throws NoSuchFieldException   if the field traversalTable does not exist
     * @throws IllegalAccessException if it was not possible to get access to the field
     * @throws NoSuchClassException   if the inner class EntryIterator does not exist
     */
    private Object[] getTraversalTableFromEntryIterator(Iterator<Entry<?, ?>> entryIterator)
            throws NoSuchFieldException, IllegalAccessException, NoSuchClassException {
        final Class<?> entryIteratorClass = getInnerClass("EntryIterator");
        final Class<?> identityHashMapIteratorClass = entryIteratorClass.getSuperclass();
        final Field traversalTableField = identityHashMapIteratorClass.getDeclaredField("traversalTable");
        traversalTableField.setAccessible(true);
        return (Object[]) traversalTableField.get(entryIterator);
    }

    /**
     * Get the private lastReturnedEntry from the IdentityHashMap$EntryIterator inner class,
     * using reflection.
     *
     * @param entryIterator an instance of the IdentityHashMap$EntryIterator
     * @return the requested lastReturnedEntry field, or {@code null} if it is not instantiated
     * @throws NoSuchFieldException   if the field lastReturnedEntry does not exist
     * @throws IllegalAccessException if it was not possible to get access to the field
     * @throws NoSuchClassException   if the inner class EntryIterator does not exist
     */
    private Entry<?, ?> getLastReturnedEntryFromEntryIterator(Iterator<Entry<?, ?>> entryIterator)
            throws NoSuchFieldException, NoSuchClassException, IllegalAccessException {
        final Class<?> entryIteratorClass = getInnerClass("EntryIterator");
        final Field lastReturnedEntryField = entryIteratorClass.getDeclaredField("lastReturnedEntry");
        lastReturnedEntryField.setAccessible(true);
        return (Entry<?, ?>) lastReturnedEntryField.get(entryIterator);
    }

    /**
     * Get the private integer field with the specified fieldName from the
     * IdentityHashMap$EntryIterator$Entry inner class, using reflection.
     *
     * @param entry     an instance of the IdentityHashMap$EntryIterator$Entry class
     * @param fieldName the name of the requested integer field
     * @return the value of the requested field
     * @throws NoSuchFieldException   if the field does not exist
     * @throws IllegalAccessException if it was not possible to get access to the field
     * @throws NoSuchClassException   if one of the expected inner classes does not exist
     */
    private Integer getIntegerFieldByNameFromEntry(Entry<?, ?> entry, String fieldName)
            throws NoSuchFieldException, IllegalAccessException, NoSuchClassException {
        final Class<?> entryIteratorClass = getInnerClass("EntryIterator");
        final Class<?> entryClass = getInnerClass(entryIteratorClass, "Entry");
        final Field declaredField = entryClass.getDeclaredField(fieldName);
        declaredField.setAccessible(true);
        return (Integer) declaredField.get(entry);
    }

    /**
     * Get the value of the private field values from the specified map's parent class
     * ({@link AbstractMap}) using reflection.
     *
     * @param map an instance of the {@link IdentityHashMap}
     * @return the content of the private field values
     * @throws NoSuchFieldException   if the field values does not exist
     * @throws IllegalAccessException if it was not possible to get access to the field
     */
    private Collection<?> getValues(IdentityHashMap<?, ?> map)
            throws NoSuchFieldException, IllegalAccessException {
        final Field valuesField = AbstractMap.class.getDeclaredField("values");
        valuesField.setAccessible(true);
        return (Collection<Object>) valuesField.get(map);
    }

    /**
     * Get the private integer field with the specified fieldName from the
     * IdentityHashMap$ValueIterator inner class, using reflection.
     *
     * @param valueIterator an instance of the IdentityHashMap$ValueIterator
     * @param fieldName     the name of the field to get the value from
     * @return the value of the requested field, or {@code null} if it is not instantiated
     * @throws NoSuchFieldException   if the requested field does not exist
     * @throws IllegalAccessException if it was not possible to ge access to the field
     * @throws NoSuchClassException   if the inner class ValueIterator does not exist
     */
    private Integer getIntegerFieldByNameFromValueIterator(Iterator<?> valueIterator, String fieldName)
            throws NoSuchFieldException, IllegalAccessException, NoSuchClassException {
        final Class<?> valueIteratorClass = getInnerClass("ValueIterator");
        Field declaredField;
        try {
            declaredField = valueIteratorClass.getDeclaredField(fieldName);
        } catch (NoSuchFieldException e) {
            final Class<?> identityHashMapIteratorClass = valueIteratorClass.getSuperclass();
            declaredField = identityHashMapIteratorClass.getDeclaredField(fieldName);
        }
        declaredField.setAccessible(true);
        return (Integer) declaredField.get(valueIterator);
    }

    /**
     * Get the traversalTable field from the IdentityHashMap$ValueIterator inner class,
     * using reflection.
     *
     * @param valueIterator an instance of the IdentityHashMap$ValueIterator
     * @return the requested traversalTable field, or {@code null} if it is not instantiated
     * @throws NoSuchFieldException   if the field traversalTable does not exist
     * @throws IllegalAccessException if it was not possible to get access to the field
     * @throws NoSuchClassException   if the inner class ValueIterator does not exist
     */
    private Object[] getTraversalTableFromValueIterator(Iterator<?> valueIterator)
            throws NoSuchFieldException, IllegalAccessException, NoSuchClassException {
        final Class<?> valueIteratorClass = getInnerClass("ValueIterator");
        final Class<?> identityHashMapIteratorClass = valueIteratorClass.getSuperclass();
        final Field traversalTableField = identityHashMapIteratorClass.getDeclaredField("traversalTable");
        traversalTableField.setAccessible(true);
        return (Object[]) traversalTableField.get(valueIterator);
    }

    /**
     * Get the content of the field keySet from the specified map's parent ({@link AbstractMap})
     * using reflection.
     *
     * @param map an instance of the {@link IdentityHashMap}
     * @return the requested set, or {@code null} if it is not instantiated
     * @throws NoSuchFieldException   if the field keySet does not exist
     * @throws IllegalAccessException if it was not possible to get access to the field
     */
    private Set<?> getKeySet(IdentityHashMap<?, ?> map)
            throws NoSuchFieldException, IllegalAccessException {
        final Field keySetField = AbstractMap.class.getDeclaredField("keySet");
        keySetField.setAccessible(true);
        return (Set<Object>) keySetField.get(map);
    }

    /**
     * Get the private integer value of the field with the specified fieldName from the
     * IdentityHashMap$KeyIterator inner class, using reflection.
     *
     * @param keyIterator an instance of the IdentityHashMap$KeyIterator
     * @param fieldName   the name of the requested field (which must be of type integer)
     * @return the value of the requested field, or {@code null} if it is not instantiated
     * @throws NoSuchFieldException   if the requested field does not exist
     * @throws IllegalAccessException if it was not possible to get access toe the field
     * @throws NoSuchClassException   if the inner class KeyIterator does not exist
     */
    private Integer getIntegerFieldByNameFromKeyIterator(Iterator<?> keyIterator, String fieldName)
            throws NoSuchFieldException, IllegalAccessException, NoSuchClassException {
        final Class<?> keyIteratorClass = getInnerClass("KeyIterator");
        final Class<?> identityHashMapIteratorClass = keyIteratorClass.getSuperclass();
        final Field declaredField = identityHashMapIteratorClass.getDeclaredField(fieldName);
        declaredField.setAccessible(true);
        return (Integer) declaredField.get(keyIterator);
    }

    /**
     * Get the private traversalTable field from the IdentityHashMap$KeyIterator inner
     * class, using reflection.
     *
     * @param keyIterator an instance of the IdentityHashMap$KeyIterator
     * @return the requested traversalTable, or {@code null} if it is not instantiated
     * @throws NoSuchFieldException   if the field traversalTable does not exist
     * @throws IllegalAccessException if it was not possible to get access to the field
     * @throws NoSuchClassException   if the inner class KeyIterator does not exist
     */
    private Object[] getTraversalTableFromKeyIterator(Iterator<?> keyIterator)
            throws NoSuchFieldException, IllegalAccessException, NoSuchClassException {
        final Class<?> keyIteratorClass = getInnerClass("KeyIterator");
        final Class<?> identityHashMapIteratorClass = keyIteratorClass.getSuperclass();
        final Field traversalTableField = identityHashMapIteratorClass.getDeclaredField("traversalTable");
        traversalTableField.setAccessible(true);
        return (Object[]) traversalTableField.get(keyIterator);
    }

    /**
     * Get the declared innerclass of the {@link IdentityHashMap} with the specified name,
     * using reflection.
     *
     * @param innerClassName the (Short) name of the inner {@link Class} to get from the
     *                       {@link IdentityHashMap} class
     * @return the requested inner class
     * @throws NoClassDefFoundError if the inner class does not exist
     */
    private Class<?> getInnerClass(String innerClassName)
            throws NoSuchClassException {
        return getInnerClass(IdentityHashMap.class, innerClassName);
    }

    /**
     * Get the declared innerclass of the specified outer class with the specified
     * inner class name, using reflection.
     *
     * @param outerClass     the outer class to search in
     * @param innerClassName the (short) name of the requested inner class
     * @return the requested inner class
     * @throws NoSuchClassException if the inner class does not exist
     */
    private Class<?> getInnerClass(Class<?> outerClass, String innerClassName)
            throws NoSuchClassException {
        final String searchName = String.format("%s$%s", outerClass.getName(), innerClassName);
        for (Class<?> clazz : outerClass.getDeclaredClasses()) {
            if (clazz.getName().equals(searchName)) return clazz;
        }
        throw new NoSuchClassException("Class " + innerClassName +
                " does not exist in " + outerClass.getName() + ".");
    }

    /**
     * Determines whether n is a power of two.
     *
     * @param n the value to probe
     * @return {@code true} if n is a power of two, or {@code false} otherwise.
     */
    private boolean isPowerOfTwo(int n) {
        return n > 0 && ((n & (n - 1)) == 0);
    }

    /**
     * An exception to be thrown when a class definition is not found, typically after
     * a failed attempt to find a class in the list resulting from a call to the method
     * {@link Class#getDeclaredClasses()}
     */
    private static class NoSuchClassException extends ReflectiveOperationException {
        NoSuchClassException(String msg) {
            super(msg);
        }
    }
}
