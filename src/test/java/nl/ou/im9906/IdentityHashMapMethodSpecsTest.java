package nl.ou.im9906;

import org.hamcrest.Matchers;
import org.junit.Before;
import org.junit.Ignore;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.ExpectedException;

import java.lang.reflect.Constructor;
import java.lang.reflect.Field;
import java.lang.reflect.InvocationTargetException;
import java.math.BigInteger;
import java.util.Arrays;
import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import static nl.ou.im9906.TestHelper.getValueByFieldName;
import static nl.ou.im9906.TestHelper.invokeMethodWithParams;
import static nl.ou.im9906.TestHelper.setValueByFieldName;
import static nl.ou.im9906.TestHelper.setValueOfFinalStaticFieldByName;
import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.core.Is.is;

/**
 * This test class tests some of the JML specs added to the {@link IdentityHashMap}
 * in the 'IM9906 VerifiyingIdentityHashMap' project that aims to formally specify
 * that class.
 * <p>
 * For example, in this test class we play call the methods in the {@link IdentityHashMap}
 * of the JDK7 (the version of the class under analysis), and try to test the JML specs
 * of these methods. This way we can perform some preliminary sanity checks on these specs
 * to see if they themselves are okay. (If one of the tests fails, there is, in theory, a
 * chance that the {@link IdentityHashMap} contains a bug, but it is more likely that the
 * JML specs (or the representation in this test class) contain an error.)
 */
public class IdentityHashMapMethodSpecsTest {

    @Rule
    public ExpectedException expectedException = ExpectedException.none();

    // The test subject
    private IdentityHashMap<Object, Object> map;

    @Before
    public void setUp() {
        map = new IdentityHashMap<>();
    }

    /**
     * Tests the postcondition of the default constructor of the {@link IdentityHashMap}. The
     * length of the private field table is expected to be 2 * DEFAULT_CAPACITY = 64, and the
     * exptected size of the map is 0.
     * </p>
     * JML specification to check:
     * <pre>
     *   public normal_behavior
     *       ensures
     *           DEFAULT_CAPACITY == 32 &&
     *           table.length == (\bigint)2 * DEFAULT_CAPACITY &&
     *           size == 0;
     * </pre>
     *
     * @throws NoSuchFieldException   if the expected private field table does not exist
     * @throws IllegalAccessException if it was not possible to get acces to the private field
     */
    @Test
    public void testDefaultConstructorPostCondition()
            throws NoSuchFieldException, IllegalAccessException {
        final int defaultCapacity = (int) getValueByFieldName(map, "DEFAULT_CAPACITY");
        assertThat(((Object[]) getValueByFieldName(map, "table")).length, is(2 * defaultCapacity));
        assertThat(map.size(), is(0));
    }

    /**
     * Tests the postcondition of the constructor of the {@link IdentityHashMap} accepting a
     * preferred capacity for an argument. When a negative value is passed, an
     * IllegalArgumentException is expected.
     * </p>
     * JML specification to check:
     * <pre>
     *     public exceptional_behavior
     *       requires
     *         expectedMaxSize < 0;
     *       signals_only
     *         IllegalArgumentException;
     *       signals
     *         (IllegalArgumentException e) true;
     * </pre>
     */
    @Test
    public void testConstructorWithPreferredCapacityExceptionalBehavior() {
        expectedException.expect(IllegalArgumentException.class);
        new IdentityHashMap<>(-1);
    }

    /**
     * Tests the postcondition of the constructor of the {@link IdentityHashMap} accepting a
     * expected max size for an argument. When a non-negative value is passed, we expect the
     * length of the table array to be determined by the capacity method.
     * </p>
     * JML specification to check:
     * <pre>
     *     public normal_behavior
     *       requires
     *         expectedMaxSize >= 0;
     *       ensures
     *         table.length == (\bigint)2 * capacity(expectedMaxSize) &&
     *         size == 0;
     * </pre>
     *
     * @throws NoSuchMethodException
     * @throws InvocationTargetException
     * @throws IllegalAccessException
     * @throws NoSuchFieldException
     */
    @Test
    public void testConstructorWithExpectedMaxSizeNormalBehavior()
            throws NoSuchMethodException, InvocationTargetException, IllegalAccessException, NoSuchFieldException, InstantiationException {
        IdentityHashMap<String, String> map = new IdentityHashMap<>(0);
        int capacity = (int) invokeMethodWithParams(map, "capacity", 0);
        assertThat(((Object[]) getValueByFieldName(map, "table")).length, is(2 * capacity));
        assertThat(map.size(), is(0));

        final int largeInt = Integer.MAX_VALUE / 1024;
        map = new IdentityHashMap<>(largeInt);
        capacity = (int) invokeMethodWithParams(map, "capacity", largeInt);
        assertThat(((Object[]) getValueByFieldName(map, "table")).length, is(2 * capacity));
        assertThat(map.size(), is(0));
    }

    /**
     * Test the exceptional_behaviour of the constructor of {@link IdentityHashMap} when
     * {@code null} is passed as a parameter.
     * </p>
     * JML specification to check:
     * <pre>
     *     public exceptional_behavior
     *       requires
     *         m == null;
     *       signals_only
     *         NullPointerException;
     *       signals
     *         (NullPointerException e) true;
     * </pre>
     */
    @Test
    public void testConstructorWithMapArgumentExceptionalBehavior() {
        expectedException.expect(NullPointerException.class);
        new IdentityHashMap<>(null);
    }

    /**
     * Checks the postcondition of the constructor of {@link IdentityHashMap} accepting
     * a {@code Map} as an input parameter, in case normal_behavior.
     * </p>
     * JML specification to check:
     * <pre>
     *     public normal_behavior
     *       requires
     *         m != null;
     *       ensures
     *         size == m.size() &&
     *         (\forall \bigint i;
     *             0 <= i < table.length - 1 && i % 2 == 0;
     *             m.get(table[i]) == table[i+1]);
     * </pre>
     * </p>
     * Also tests the pureness of the constructor, meaning (in terms of JML):
     * <pre>
     *     assignable this.*;
     * </pre>
     *
     * @throws InvocationTargetException
     * @throws NoSuchMethodException
     * @throws InstantiationException
     * @throws IllegalAccessException
     */
    @Test
    public void testConstructorWithMapArgumentNormalBehavior()
            throws InvocationTargetException, NoSuchMethodException, InstantiationException, IllegalAccessException, NoSuchFieldException {
        final Map<String, String> paramMap = new HashMap<>();
        paramMap.put("aKey", "aValue");
        paramMap.put("anotherKey", "anotherValue");

        final IdentityHashMap<String, String> map = new IdentityHashMap<>(paramMap);

        // Check the size and the table content
        assertThat(map.size(), is(paramMap.size()));
        final Object[] table = (Object[]) getValueByFieldName(map, "table");
        for (int i = 0; i < table.length; i += 2) {
            assertThat(paramMap.get(table[i]), is(table[i + 1]));
        }

        // Test the pureness of this constructor. The input map is not assignable,
        // meaning the data group as a whole will not be changed.
        assertIsPureConstructor(paramMap);
    }

    /**
     * Tests it the private method {@code capacity} of the {@link IdentityHashMap}
     * is pure.
     *
     * @throws NoSuchMethodException
     * @throws IllegalAccessException
     * @throws NoSuchFieldException
     */
    @Test
    public void testCapacityPostcondition()
            throws NoSuchMethodException, IllegalAccessException, NoSuchFieldException {
        assertIsPureMethod(map, "capacity", 32);
    }

    /**
     * Tests the postconditions of the init method of the {@link IdentityHashMap}.
     * Pre-conditions are: capacity must be a power of 2, and must be between
     * MINIMUM_CAPACITY and MAXIMUM_CAPACITY, and size must be 0.
     * Postconditions are: threshold must have a value (2 * capacity) / 3, the
     * lenght of the table array must be 2 * capacity, and the size must be unchanged.
     *
     * @throws NoSuchMethodException
     * @throws InvocationTargetException
     * @throws IllegalAccessException
     * @throws NoSuchFieldException
     */
    @Test
    public void testInitPostCondition()
            throws NoSuchMethodException, IllegalAccessException, InvocationTargetException, NoSuchFieldException {
        // Small capacity
        assertInitPostconditions((int) getValueByFieldName(map, "MINIMUM_CAPACITY"));
        // Medium capacity
        assertInitPostconditions((int) getValueByFieldName(map, "DEFAULT_CAPACITY"));
        // Large capacity
        assertInitPostconditions(Integer.MAX_VALUE / 1024);
    }

    /**
     * Tests the postconditions of the size method of the {@link IdentityHashMap}.
     * The size method is a pure method and has no side effects. This will also be
     * tested by checking if none of the fields will be altered.
     * </p>
     * JML specification to check:
     * <pre>
     *   also
     *     public normal_behavior
     *       ensures
     *         \result == size;
     * </pre>
     * Also tests the pureness of the constructor, meaning (in terms of JML):
     * <pre>
     *     assignable \nothing;
     * </pre>
     *
     * @throws NoSuchFieldException
     * @throws IllegalAccessException
     * @throws NoSuchMethodException
     */
    @Test
    public void testSizePostcondition()
            throws NoSuchFieldException, IllegalAccessException, NoSuchMethodException {
        assertThat(map.size(), is(0));
        setValueByFieldName(map, "size", 1024);
        assertThat(map.size(), is(1024));

        // Test if the size method is really pure
        assertIsPureMethod(map, "size");
    }

    /**
     * Tests the postconditions of the isEmpty method of the {@link IdentityHashMap}.
     * The isEmpty method is a pure method and has no side effects. This will also be
     * tested by checking if none of the fields will be altered.
     * </p>
     * JML specification to test:
     * <pre>
     *     also
     *       public normal_behavior
     *         ensures
     *           \result <==> size == 0;
     * </pre>
     * Also tests the pureness of the constructor, meaning (in terms of JML):
     * <pre>
     *     assignable \nothing;
     * </pre>
     *
     * @throws NoSuchFieldException
     * @throws IllegalAccessException
     * @throws NoSuchMethodException
     */
    @Test
    public void testIsEmptyPostcondition()
            throws NoSuchFieldException, IllegalAccessException, NoSuchMethodException {
        assertThat(map.isEmpty(), is(true));
        setValueByFieldName(map, "size", 1);
        assertThat(map.isEmpty(), is(false));

        // Test if the isEmpty method is really pure
        assertIsPureMethod(map, "isEmpty");
    }

    /**
     * Tests if the hash method of the {@link IdentityHashMap} is a pure method, as
     * specified in the JML.
     *
     * @throws NoSuchMethodException
     * @throws IllegalAccessException
     * @throws NoSuchFieldException
     */
    @Test
    public void testHashPostcondition()
            throws NoSuchMethodException, IllegalAccessException, NoSuchFieldException {
        assertIsPureMethod(map, "hash", new Object(), 32);
    }

    /**
     * Test if the nextKeyIndex method of the {@link IdentityHashMap} is a pure
     * method, and if the JML postcondition holds for several cases.
     *
     * @throws InvocationTargetException
     * @throws NoSuchMethodException
     * @throws IllegalAccessException
     * @throws NoSuchFieldException
     */
    @Test
    public void testNextKeyIndexPostcondition()
            throws InvocationTargetException, NoSuchMethodException, IllegalAccessException, NoSuchFieldException {
        final int i = Integer.MAX_VALUE - 2;
        final int j = 8;
        assertNextKeyIndexPostCondition(i, j);
        assertNextKeyIndexPostCondition(j, j);
        assertNextKeyIndexPostCondition(i, i);
        assertNextKeyIndexPostCondition(j, i);
    }

    /**
     * Test if the postcondition in the JML for the get method of the {@link IdentityHashMap}
     * holds for several cases. Also, the pureness of the method is tested.
     *
     * @throws InvocationTargetException
     * @throws NoSuchMethodException
     * @throws IllegalAccessException
     * @throws NoSuchFieldException
     */
    @Test
    public void testGetPostcondition()
            throws InvocationTargetException, NoSuchMethodException, IllegalAccessException, NoSuchFieldException {
        assertGetPostConditionForNonNullResult(map);
        assertGetPostConditionForNullResult(map);
    }

    /**
     * Checks if the postcondition for the containsKey method of the {@link IdentityHashMap}
     * holds whether or not a key is present in the table. Also, the pureness of the method is
     * tested.
     *
     * @param map the map to call the containsKey method on
     * @throws NoSuchFieldException
     * @throws IllegalAccessException
     * @throws InvocationTargetException
     * @throws NoSuchMethodException
     */
    @Test
    public void testContainsKeyPostcondition()
            throws InvocationTargetException, NoSuchMethodException, IllegalAccessException, NoSuchFieldException {
        // Assert that the following postcondition for the containsKey call on map holds:
        //    \result <==> (\exists \bigint i;
        //        0 <= i < table.length - 1 && i % 2 == 0;
        //        table[i] == key);
        assertContainsKeyPostConditionFound(map);
        assertContainsKeyPostConditionNotFound(map);
    }

    /**
     * Checks if the postcondition for the containsValue method of the {@link IdentityHashMap}
     * holds whether or not a value is present in the table. Also, the pureness of the method is
     * tested.
     *
     * @param map the map to call the containsValue method on
     * @throws NoSuchFieldException
     * @throws IllegalAccessException
     * @throws InvocationTargetException
     * @throws NoSuchMethodException
     */
    @Test
    public void testContainsValuePostcondition()
            throws InvocationTargetException, NoSuchMethodException, IllegalAccessException, NoSuchFieldException {
        // Assert that the following postcondition for the containsValue call on map holds:
        //    \result <==> (\exists \bigint i;
        //        1 <= i < table.length && i % 2 == 0;
        //        table[i] == value);
        assertContainsValuePostConditionFound(map);
        assertContainsValuePostConditionNotFound(map);
    }

    /**
     * Checks if the postcondition for the containsMapping method of the {@link IdentityHashMap}
     * holds whether or not a mapping (key-value pair) is present in the table. Also tests if
     * the method is pure.
     *
     * @param map the map to call the containsMapping method on
     * @throws NoSuchFieldException
     * @throws IllegalAccessException
     * @throws InvocationTargetException
     * @throws NoSuchMethodException
     */
    @Test
    public void testContainsMappingPostcondition()
            throws InvocationTargetException, NoSuchMethodException, IllegalAccessException, NoSuchFieldException {
        // Assert that the following postcondition for the containsEntry call on map holds:
        //    \result <==> (\exists \bigint i;
        //        0 <= i < table.length - 1 && i % 2 == 0;
        //        table[i] == key && table[i + 1] == value);
        assertContainsMappingPostConditionFound(map);
        assertContainsMappingPostConditionNotFound(map);
    }

    /**
     * Tests that a {@link IllegalStateException} is being thrown when the table
     * cannot be resized.
     *
     * @throws NoSuchFieldException
     * @throws IllegalAccessException
     * @throws InvocationTargetException
     * @throws NoSuchMethodException
     */
    @Test
    @Ignore // TODO: Assigning a value to a final static does not have the expected effect on the program flow.
    public void testResizeExceptionalbehavior()
            throws NoSuchFieldException, IllegalAccessException, InvocationTargetException, NoSuchMethodException {
        final int maxCapacity = 1024;
        //TODO: setValueOfFinalStaticFieldByName(IdentityHashMap.class, "MAXIMUM_CAPACITY", maxCapacity);

        final Object[] tableThatCantBeExpanded = new Object[maxCapacity * 2];
        setValueByFieldName(map, "table", tableThatCantBeExpanded);
        setValueByFieldName(map, "threshold", maxCapacity - 1);

        expectedException.expect(IllegalStateException.class);
        expectedException.expectMessage("Capacity exhausted.");

        invokeMethodWithParams(map, "resize", 0);
    }

    /**
     * Test the postcondition of the resize method of the {@link IdentityHashMap} in case
     * of normal behaviour.
     * </p>
     * JML specification to check:
     * <pre>
     *     ensures
     *       \old(table.length) == (\bigint)2 * MAXIMUM_CAPACITY ==>
     *           (threshold == MAXIMUM_CAPACITY - (\bigint)1 && table.length == \old(table.length)) &&
     *       (\old(table.length) != (\bigint)2 * MAXIMUM_CAPACITY && \old(table.length) >= (newCapacity * (\bigint)2)) ==>
     *           table.length == \old(table.length) &&
     *       (\old(table.length) != (\bigint)2 * MAXIMUM_CAPACITY && \old(table.length) < (newCapacity * (\bigint)2)) ==>
     *           table.length == (newCapacity * (\bigint)2) &&
     *       (\forall \bigint i;
     *           0 <= i < \old(table.length) - 1 && i % 2 == 0;
     *              (\exists \bigint j;
     *                   0 <= j < table.length - 1 && j % 2 == 0;
     *                   table[i] == \old(table[j]) && table[i + 1] == \old(table[j + 1])));
     * </pre>
     * Note: skipping tests with large tables (MAXIMUM_CAPACITY) due to max memory errors.
     *
     * @throws NoSuchFieldException
     * @throws IllegalAccessException
     * @throws InvocationTargetException
     * @throws NoSuchMethodException
     */
    @Test
    public void testResizeNormalBehavior()
            throws NoSuchFieldException, IllegalAccessException, InvocationTargetException, NoSuchMethodException {
        final int minCapacity = (int) getValueByFieldName(map, "MINIMUM_CAPACITY");
        final Object[] table = new Object[minCapacity * 2];
        setValueByFieldName(map, "table", table);
        setValueByFieldName(map, "threshold", minCapacity - 1);

        // newCapacity * 2 < length of \old(table) -> don't resize
        final Object[] oldTable = (Object[])getValueByFieldName(map, "table");
        invokeMethodWithParams(map, "resize", 0);
        Object[] newTable = (Object[])getValueByFieldName(map, "table");
        assertThat(newTable.length, is(oldTable.length));

        // newCapacity * 2 == length of \old(table) -> don't resize
        invokeMethodWithParams(map, "resize", oldTable.length / 2);
        newTable = (Object[])getValueByFieldName(map, "table");
        assertThat(newTable.length, is(oldTable.length));

        // newCapacity * 2 > length of \old(table) -> do resize
        invokeMethodWithParams(map, "resize", oldTable.length);
        newTable = (Object[])getValueByFieldName(map, "table");
        assertThat(newTable.length, is(2 * oldTable.length));
        for (int i = 0; i < oldTable.length; i++) {
            // Check if all the keys and values are still present in the same location.
            assertThat(oldTable[i] == newTable[i], is(true));
        }

        // Assert that no other fields are assgined a value that "trheshold" and "table",
        // validating the JML clause:
        //     \assignable
        //         threshold, table.
        assertAssignableClause(map, "resize", new Integer[]{0}, new String[]{"threshold", "table"}, new int[0]);
    }

    /**
     * Tests if a {@link NullPointerException} is thrown when a {@code null} is passed
     * as parameter to the putAll method of the {@link IdentityHashMap}.
     * </p>
     * JML specification to test:
     * <pre>
     *     public exceptional_behavior
     *       requires
     *         m == null;
     *       assignable
     *         \nothing;
     *       signals_only
     *         NullPointerException;
     *       signals
     *         (NullPointerException e) true;
     * </pre>
     */
    @Test
    public void testPutAllExceptionalBehaviour()
            throws NoSuchMethodException, NoSuchFieldException, IllegalAccessException, InvocationTargetException {
        // Check the asignable clause
        assertAssignableNothingClause(map, "putAll", new Object[]{null});

        // Check for the NullPointerException
        expectedException.expect(NullPointerException.class);
        map.putAll(null);
    }

    @Test
    public void testPutAllNormalBehavior()
            throws IllegalAccessException, NoSuchFieldException, NoSuchMethodException {
        // TODO

        // Check the JML assignable clause
        final Map<String, String>[] params = new Map[1];
        params[0] = new HashMap<>();
        params[0].put("aKey", "aValue");
        assertAssignableClause(map, "putAll", params,
                new String[]{"threshold", "table", "size", "modCount"}, new int[]{1}
        );
    }

    @Test
    public void testRemovePostCondition() {
        // TODO
    }

    @Test
    public void testRemoveMappingPostCondition() {
        // TODO
    }

    @Test
    public void testCloseDeletionPostCondition() {
        // TODO
    }

    @Test
    public void testClearPostCondition() {
        // TODO
    }

    @Test
    public void testEqualsPostcondition()
            throws NoSuchMethodException, IllegalAccessException, NoSuchFieldException {
        final IdentityHashMap<String, String> map2 = new IdentityHashMap<>();
        // TODO

        // Test if the equals method is really pure
        assertIsPureMethod(map, "equals", map2);
    }

    @Test
    public void testHashCodePostcondition()
            throws NoSuchMethodException, IllegalAccessException, NoSuchFieldException {
        // TODO

        // Test if the hash method is really pure
        assertIsPureMethod(map, "hashCode");
    }

    @Test
    public void testClonePostcondition()
            throws NoSuchMethodException, IllegalAccessException, NoSuchFieldException {
        // Test if the clone method is really pure
        assertIsPureMethod(map, "clone");
    }

    /**
     * Checks if the postcondition for the containsKey method of the {@link IdentityHashMap}
     * holds when a key is present in the table.
     *
     * @param map the map to call the containsKey method on
     * @throws NoSuchFieldException
     * @throws IllegalAccessException
     * @throws NoSuchMethodException
     */
    private void assertContainsKeyPostConditionFound(IdentityHashMap<Object, Object> map)
            throws NoSuchFieldException, IllegalAccessException, NoSuchMethodException {
        final String key = "aKey";
        map.put(key, "aValue");

        final boolean found = keyExistsInTable(map, key);
        assertThat(map.containsKey(key), is(found));
        assertThat(found, is(true));

        // Test if the containsKey method is really pure
        assertIsPureMethod(map, "containsKey", key);
    }

    /**
     * Checks if the postcondition for the containsKey method of the {@link IdentityHashMap}
     * holds when a key is not present in the table.
     *
     * @param map the map to call the containsKey method on
     * @throws NoSuchFieldException
     * @throws IllegalAccessException
     * @throws NoSuchMethodException
     */
    private void assertContainsKeyPostConditionNotFound(IdentityHashMap<Object, Object> map)
            throws NoSuchFieldException, IllegalAccessException, NoSuchMethodException {
        final String key = "aKey";
        map.put(key, "aValue");
        final String anotherKey = "anotherKey";

        final boolean found = keyExistsInTable(map, anotherKey);
        assertThat(map.containsKey(anotherKey), is(found));
        assertThat(found, is(false));

        // Test if the containsKey method is really pure
        assertIsPureMethod(map, "containsKey", anotherKey);
    }

    /**
     * Checks if the postcondition for the containsValue method of the {@link IdentityHashMap}
     * holds when a value is present in the table.
     *
     * @param map the map to call the containsValue method on
     * @throws NoSuchFieldException
     * @throws IllegalAccessException
     * @throws NoSuchMethodException
     */
    private void assertContainsValuePostConditionFound(IdentityHashMap<Object, Object> map)
            throws NoSuchFieldException, IllegalAccessException, NoSuchMethodException {
        final String key = "aKey";
        final String value = "aValue";
        map.put(key, value);

        final boolean found = valueExistsInTable(map, value);
        assertThat(map.containsValue(value), is(found));
        assertThat(found, is(true));

        // Test if the containsKey method is really pure
        assertIsPureMethod(map, "containsValue", value);
    }

    /**
     * Checks if the postcondition for the containsValue method of the {@link IdentityHashMap}
     * holds when a value is not present in the table.
     *
     * @param map the map to call the containsValue method on
     * @throws NoSuchFieldException
     * @throws IllegalAccessException
     * @throws NoSuchMethodException
     */
    private void assertContainsValuePostConditionNotFound(IdentityHashMap<Object, Object> map)
            throws NoSuchFieldException, IllegalAccessException, NoSuchMethodException {
        final String key = "aKey";
        final String value = "aValue";
        map.put(key, value);
        final String anotherValue = "anotherValue";

        final boolean found = valueExistsInTable(map, anotherValue);
        assertThat(map.containsValue(anotherValue), is(found));
        assertThat(found, is(false));

        // Test if the containsKey method is really pure
        assertIsPureMethod(map, "containsValue", anotherValue);
    }

    /**
     * Checks if the postcondition for the containsMapping method of the {@link IdentityHashMap}
     * holds when a mapping is present in the table.
     *
     * @param map the map to call the containsMapping method on
     * @throws NoSuchFieldException
     * @throws IllegalAccessException
     * @throws InvocationTargetException
     * @throws NoSuchMethodException
     */
    private void assertContainsMappingPostConditionFound(IdentityHashMap<Object, Object> map)
            throws NoSuchFieldException, IllegalAccessException, InvocationTargetException, NoSuchMethodException {
        final String key = "aKey";
        final String value = "aValue";
        map.put(key, value);

        final boolean found = mappingExistsInTable(map, key, value);
        assertThat((Boolean) invokeMethodWithParams(map, "containsMapping", key, value), is(found));
        assertThat(found, is(true));

        // Test if the containsKey method is really pure
        assertIsPureMethod(map, "containsMapping", key, value);
    }

    /**
     * Checks if the postcondition for the containsMapping method of the {@link IdentityHashMap}
     * holds when a mapping is NOT present in the table.
     *
     * @param map the map to call the containsMapping method on
     * @throws NoSuchFieldException
     * @throws IllegalAccessException
     * @throws InvocationTargetException
     * @throws NoSuchMethodException
     */
    private void assertContainsMappingPostConditionNotFound(IdentityHashMap<Object, Object> map)
            throws NoSuchFieldException, IllegalAccessException, InvocationTargetException, NoSuchMethodException {
        final String key = "aKey";
        final String value = "aValue";
        map.put(key, value);
        final String anotherValue = "anotherValue";

        final boolean found = mappingExistsInTable(map, key, anotherValue);
        assertThat((Boolean) invokeMethodWithParams(map, "containsMapping", key, anotherValue), is(found));
        assertThat(found, is(false));

        // Test if the containsKey method is really pure
        assertIsPureMethod(map, "containsMapping", key, anotherValue);
    }

    /**
     * Checks if the postcondition for the get method of the {@link IdentityHashMap} holds
     * when a non-{@code null} value is found and returned as a result.
     *
     * @param map the map to call the get method on
     * @throws NoSuchFieldException
     * @throws IllegalAccessException
     * @throws NoSuchMethodException
     */
    private void assertGetPostConditionForNonNullResult(IdentityHashMap<Object, Object> map)
            throws NoSuchFieldException, IllegalAccessException, NoSuchMethodException {
        final String key = "key";
        final String val = "val";
        map.put(key, val);

        // Assert that the following postcondition holds:
        //   \result != null <==>
        //       (\exists \bigint i;
        //           0 <= i < table.length - 1 && i % 2 == 0;
        //           table[i] == key && \result == table[i + 1])
        final boolean found = mappingExistsInTable(map, key, val);
        assertThat(map.get(key) != null && found, is(true));

        // Test if the get method is pure
        assertIsPureMethod(map, "get", key);
    }

    /**
     * Checks if the postcondition for the get method of the {@link IdentityHashMap} holds
     * when a {@code null} value is found and returned as a result.
     *
     * @param map the map to call the get method on
     * @throws NoSuchFieldException
     * @throws IllegalAccessException
     * @throws NoSuchMethodException
     */
    private void assertGetPostConditionForNullResult(IdentityHashMap<Object, Object> map)
            throws NoSuchFieldException, IllegalAccessException, NoSuchMethodException {
        // Assert that the following postcondition holds:
        //     \result == null <==>
        //         (!(\exists \bigint i;
        //             0 <= i < table.length - 1 && i % 2 == 0;
        //             table[i] == key) ||
        //        (\exists \bigint i;
        //             0 <= i < table.length - 1 && i % 2 == 0;
        //             table[i] == key && table[i + 1] == null)
        //         );
        assertGetPostConditionKeyNotFound(map);
        assertGetPostConditionValueNull(map);
    }

    /**
     * Checks if the postcondition for the get method of the {@link IdentityHashMap} holds
     * when a {@code null} value is found and returned as a result, because the key is not
     * found.
     *
     * @param map the map to call the get method on
     * @throws NoSuchFieldException
     * @throws IllegalAccessException
     * @throws NoSuchMethodException
     */
    private void assertGetPostConditionKeyNotFound(IdentityHashMap<Object, Object> map)
            throws NoSuchFieldException, IllegalAccessException, NoSuchMethodException {
        final String key = "aKey";
        final String anotherKey = new String("aKey");
        final String val = "aValue";
        map.put(key, val);

        final boolean valueFound = mappingExistsInTable(map, anotherKey, val);
        assertThat(map.get(anotherKey) == null, is(true));
        assertThat(valueFound, is(false));

        // Test if the get method is really pure
        assertIsPureMethod(map, "get", key);
    }

    /**
     * Checks if the postcondition for the get method of the {@link IdentityHashMap} holds
     * when a {@code null} value is found and returned as a result, because however the key
     * is found, the value is actually {@code null}.
     *
     * @param map the map to call the get method on
     * @throws NoSuchFieldException
     * @throws IllegalAccessException
     * @throws NoSuchMethodException
     */
    private void assertGetPostConditionValueNull(IdentityHashMap<Object, Object> map)
            throws NoSuchFieldException, IllegalAccessException, NoSuchMethodException {
        final String key = "KEY";
        final String val = null;
        map.put(key, val);

        final boolean valueFound = mappingExistsInTable(map, key, val);
        assertThat(map.get(key) == null, is(true));
        assertThat(valueFound, is(true));

        // Test if the get method is really pure
        assertIsPureMethod(map, "get", key);
    }

    /**
     * Checks the postcondition of the nextKeyIndex method, based on two parameters:
     * the current index, and the length of the table array.
     *
     * @param i   the current index
     * @param len the length of the array to find the next index in
     * @throws IllegalAccessException
     * @throws InvocationTargetException
     * @throws NoSuchMethodException
     * @throws NoSuchFieldException
     */
    private void assertNextKeyIndexPostCondition(int i, int len)
            throws IllegalAccessException, InvocationTargetException, NoSuchMethodException, NoSuchFieldException {
        final int result = (int) invokeMethodWithParams(map, "nextKeyIndex", i, len);

        // Assert that the following postcondition holds:
        //     \result < len &&
        //     \result >= 0 &&
        //     \result % (\bigint)2 == 0 &&
        //     i + (\bigint)2 < len ==> \result == i + (\bigint)2 &&
        //     i + (\bigint)2 >= len ==> \result == 0;
        assertThat(result, Matchers.lessThan(len));
        assertThat(result, Matchers.greaterThanOrEqualTo(0));
        assertThat(result % 2, is(0));
        final BigInteger iBigAddTwo = BigInteger.valueOf((long) i).add(BigInteger.valueOf(2));
        final BigInteger lenBig = BigInteger.valueOf(len);
        if (iBigAddTwo.compareTo(lenBig) < 0) assertThat(result, is(i + 2));
        if (iBigAddTwo.compareTo(lenBig) >= 0) assertThat(result, is(0));

        // Test if the nextKeyIndex method is pure
        assertIsPureMethod(map, "nextKeyIndex", i, len);
    }

    /**
     * Asserts that no fields and no parameters are assigned a value during the processing of the
     * method under analysis. This conforms to the JML clause: {@code assignable \nothing}. This
     * is more or less a purity check for methods. The only difference is that pure methods also
     * conform to the JML clause: {@code \diverges false}.
     *
     * @param map                    an {@link IdentityHashMap} instance, to invoke the method
     *                               under analysis on
     * @param methodName             the method under analysis
     * @param params                 the actual parameters that will be passed to the method
     * @throws NoSuchMethodException
     * @throws IllegalAccessException
     * @throws NoSuchFieldException
     */
    private void assertAssignableNothingClause(IdentityHashMap<Object, Object> map, String methodName, Object[] params)
            throws NoSuchMethodException, IllegalAccessException, NoSuchFieldException {
        this.assertAssignableClause(map, methodName, params, new String[0], new int[0]);
    }

    /**
     * Asserts that fields and/or parameters that are not assignable according to the JML
     * specification, do not get assigned a new value during the invocation of the method
     * under analysis.
     * </p>
     * Example: the JML specification clause {@code assignable threshold, table;} for the
     * method under test {@code init} would be testable by the following call to this method:
     * {@code assertAssignableClause(aMap, "init", new Integer[]{1024}, new String[]{"threshold", "table"}, new int[0]);}
     * </p>
     * Note 1: {@link InvocationTargetException}s are ignored. It might be the case that during invocation
     * of the method an exception is thrown. This might be expected behaviour; we might be testing
     * the assignable clause for exceptional_bevavior (in terms of JML), and we still want to check
     * the parameters and fields, regardless of any exception during invocation.
     * </p>
     * Note 2: comparison of fields and parameters is done based on the {@code toString()} of their
     * values. We do a {@code toString} of the value before invocation of the specified method, and
     * afterwards. We expect values that are not to be assigned to have the same string value before
     * and after. This is our way of "cloning" an object before and compare it with the object after
     * invocation of the method under analysis. Note this check only works for primitive fields and
     * parameters and for fields that are of a class that has a proper {@code toString} implementation.
     *
     * @param map                    an {@link IdentityHashMap} instance, to invoke the method
     *                               under analysis on
     * @param methodName             the method under analysis
     * @param params                 the actual parameters that will be passed to the method
     * @param assignableFieldNames   the names of the fields in the {@link IdentityHashMap}
     *                               that are assignable. Fields with these names will not be
     *                               checked for alteration. All other fields will be checked
     *                               for alteration.
     * @param assignableParamIndices the indices (starting at 0) of the parameters that are
     *                               assignable. Assignable parameters will not be checked
     *                               for alteration.
     * @throws NoSuchFieldException
     * @throws IllegalAccessException
     * @throws NoSuchMethodException
     */
    private void assertAssignableClause(IdentityHashMap<Object, Object> map, String methodName, Object[] params,
                                        String[] assignableFieldNames, int[] assignableParamIndices)
            throws NoSuchFieldException, IllegalAccessException, NoSuchMethodException {

        // Collect the fields in the IdentityHashMap: fields, their names, and their
        // values before invoking the method under test.
        final Field[] fields = map.getClass().getDeclaredFields();
        final String[] fieldNames = new String[fields.length];
        final String[] oldFieldValuesAsString = new String[fields.length];
        for (int i = 0; i < fields.length; i++) {
            fieldNames[i] = fields[i].getName();
            oldFieldValuesAsString[i] = String.valueOf(getValueByFieldName(map, fieldNames[i]));
        }

        // Collect the actual parameters passed to the method under test: their values
        // before invoking the method.
        final String[] oldParamValuesAsString = new String[params.length];
        for (int i = 0; i < params.length; i++) {
            oldParamValuesAsString[i] = String.valueOf(params[i]);
        }

        // Now, invoke the method under analysis.
        try {
            invokeMethodWithParams(map, methodName, params);
        } catch (InvocationTargetException e) {
            // This might be due to an Exception that is expected in the exceptional_behavior
            // clause of the JML. We still want to check the JML assignable clause.
            // So, let's do nothing, and resume to check the fields and parameters.
        }

        // Check if the fields have not been unexpectedly assigned a value. Compare
        // the old value with the current value.
        for (int i = 0; i < fieldNames.length; i++) {
            // Skip assignable fields for equality check
            if (!Arrays.asList(assignableFieldNames).contains(fieldNames[i])) {
                assertThat(
                        String.format("Field '%s' was unexpectedly changed.", fieldNames[i]),
                        String.valueOf(getValueByFieldName(map, fieldNames[i])),
                        is(oldFieldValuesAsString[i])
                );
            }
        }

        // Check that the parameters have not been unexpectedly assigned a value. Compare
        // the old value with the current value.
        for (int i = 0; i < params.length; i++) {
            // Skip assignable parameters for equality check
            if (!Arrays.asList(assignableParamIndices).contains(i)) {
                assertThat(
                        String.format("Parameter #%d was unexpectedly changed.", i),
                        String.valueOf(params[i]),
                        is(oldParamValuesAsString[i])
                );
            }
        }
    }

    /**
     * Asserts that a method is pure, i.e. does not have any side effect.
     *
     * @param map        the test subject
     * @param methodName the name of the method we expect to be pure
     * @param params     the actual parameters passed to the method
     * @throws NoSuchFieldException      if one or more fields do not exist
     * @throws IllegalAccessException    if one or more field cannot be accessed
     * @throws NoSuchMethodException     if the method to invoke does not exist
     * @throws InvocationTargetException if the method to invoke throws an exception
     */
    private void assertIsPureMethod(IdentityHashMap<Object, Object> map, String methodName, Object... params)
            throws NoSuchFieldException, IllegalAccessException, NoSuchMethodException {
        assertAssignableNothingClause(map, methodName, params);
    }

    /**
     * Asserts that a {@link IdentityHashMap} constructor is pure, i.e. does
     * not have any side effect, other than updating instance variables of
     * the class itself (this.*). Effectively it is not allowed to alter
     * any of the passed parameters.
     *
     * @param map an actual parameters passed to the constructor
     * @throws IllegalAccessException
     * @throws InvocationTargetException
     * @throws NoSuchMethodException
     * @throws InstantiationException
     */
    private void assertIsPureConstructor(Map<?, ?> map)
            throws IllegalAccessException, InvocationTargetException, NoSuchMethodException, InstantiationException {
        final String oldMapAsString = map.toString();
        final Constructor<?> constructor = IdentityHashMap.class.getDeclaredConstructor(Map.class);
        constructor.setAccessible(true);
        constructor.newInstance(map);
        assertThat(map.toString(), is(oldMapAsString));
    }

    /**
     * Checks the postcondition after invoking the init method of the {@link IdentityHashMap} class.
     *
     * @param initCapacity the actual parameter to pass to the init method
     * @throws NoSuchFieldException      if one or more fields do not exist
     * @throws IllegalAccessException    if one or more field cannot be accessed
     * @throws NoSuchMethodException     if the method to invoke does not exist
     * @throws InvocationTargetException if the method to invoke throws an exception
     */
    private void assertInitPostconditions(int initCapacity)
            throws NoSuchFieldException, IllegalAccessException, NoSuchMethodException, InvocationTargetException {
        invokeMethodWithParams(map, "init", initCapacity);

        // Assert that the JML postcodition of the init method holds:
        //   ensures
        //     threshold == ((\bigint)2 * initCapacity) / (\bigint)3 &&
        //     table.length == (\bigint)2 * initCapacity;
        assertThat((int) getValueByFieldName(map, "threshold"), is((initCapacity * 2) / 3));
        assertThat(((Object[]) getValueByFieldName(map, "table")).length, is(initCapacity * 2));

        // Assert that no other fields are assgined a value that "trheshold" and "table",
        // validating the JML clause:
        //     \assignable
        //         threshold, table.
        assertAssignableClause(map, "init", new Integer[]{initCapacity}, new String[]{"threshold", "table"}, new int[0]);
    }

    /**
     * Determines whether a specified key is present in the {@link IdentityHashMap}'s
     * table array field.
     *
     * @param map instance of the {@link IdentityHashMap} to search in
     * @param key the key to search
     * @return {@code true} if found, {@code false} otherwise
     * @throws NoSuchFieldException
     * @throws IllegalAccessException
     */
    private boolean keyExistsInTable(IdentityHashMap<?, ?> map, Object key)
            throws NoSuchFieldException, IllegalAccessException {
        final Object[] table = (Object[]) getValueByFieldName(map, "table");
        for (int i = 0; i < table.length - 1; i += 2) {
            if (table[i] == key) {
                return true;
            }
        }
        return false;
    }

    /**
     * Determines whether a specified value is present in the {@link IdentityHashMap}'s
     * table array field.
     *
     * @param map instance of the {@link IdentityHashMap} to search in
     * @param val the value to search
     * @return {@code true} if found, {@code false} otherwise
     * @throws NoSuchFieldException
     * @throws IllegalAccessException
     */
    private boolean valueExistsInTable(IdentityHashMap<?, ?> map, Object val)
            throws NoSuchFieldException, IllegalAccessException {
        final Object[] table = (Object[]) getValueByFieldName(map, "table");
        for (int i = 1; i < table.length; i += 2) {
            if (table[i] == val) {
                return true;
            }
        }
        return false;
    }

    /**
     * Determines whether a specified key-value pair is present in the {@link IdentityHashMap}'s
     * table array field.
     *
     * @param map instance of the {@link IdentityHashMap} to search in
     * @param key the key to search
     * @param val the value to seach
     * @return {@code true} if found, {@code false} otherwise
     * @throws NoSuchFieldException
     * @throws IllegalAccessException
     */
    private boolean mappingExistsInTable(IdentityHashMap<Object, Object> map, Object key, Object val)
            throws NoSuchFieldException, IllegalAccessException {
        final Object[] table = (Object[]) getValueByFieldName(map, "table");
        for (int i = 0; i < table.length - 1; i += 2) {
            if (table[i] == key && table[i + 1] == val) {
                return true;
            }
        }
        return false;
    }

}
