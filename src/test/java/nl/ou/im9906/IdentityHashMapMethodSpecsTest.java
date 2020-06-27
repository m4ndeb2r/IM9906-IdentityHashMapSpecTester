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

    // Set this constant to true for extra output
    private static final boolean VERBOSE = true;

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

    @Test
    public void testConstructorWithMapArgumentNormalBehavior()
            throws InvocationTargetException, NoSuchMethodException, InstantiationException, IllegalAccessException {
        // TODO: for now, we just test the pureness of this constructor. Add more checks
        final Map<String, String> paramMap = new HashMap<>();
        paramMap.put("aKey", "aValue");
        assertIsPureConstructor(paramMap);
    }

    @Test
    public void testConstructorWithMapArgumentExceptionalBehavior() {
        // TODO; test for NullPointerException
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
     *
     * @throws NoSuchFieldException
     * @throws IllegalAccessException
     */
    @Test
    public void testSizePostcondition()
            throws NoSuchFieldException, IllegalAccessException, InvocationTargetException, NoSuchMethodException {
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
     *
     * @throws NoSuchFieldException
     * @throws IllegalAccessException
     */
    @Test
    public void testIsEmptyPostcondition()
            throws NoSuchFieldException, IllegalAccessException, InvocationTargetException, NoSuchMethodException {
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
     * @throws InvocationTargetException
     * @throws NoSuchMethodException
     * @throws IllegalAccessException
     * @throws NoSuchFieldException
     */
    @Test
    public void testHashPostcondition()
            throws InvocationTargetException, NoSuchMethodException, IllegalAccessException, NoSuchFieldException {
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
     * holds for several cases.
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
     * holds whether or not a key is present in the table.
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
     * holds whether or not a value is present in the table.
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
     * holds whether or not a mapping (key-value pair) is present in the table.
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
     * Test that a {@link IllegalStateException} is being thrown when the table
     * cannot be resized.
     *
     * @throws NoSuchFieldException
     * @throws IllegalAccessException
     * @throws InvocationTargetException
     * @throws NoSuchMethodException
     */
    @Test
    @Ignore // OutOfMemoryError when running this test
    public void testResizeExceptionalbehavior()
            throws NoSuchFieldException, IllegalAccessException, InvocationTargetException, NoSuchMethodException {
        final int maxCapacity = (int) getValueByFieldName(map, "MAXIMUM_CAPACITY");
        final Object[] tableThatCantBeExpanded = new Object[maxCapacity * 2];
        setValueByFieldName(map, "table", tableThatCantBeExpanded);
        setValueByFieldName(map, "threshold", maxCapacity - 1);

        expectedException.expect(IllegalStateException.class);
        expectedException.expectMessage("Capacity exhausted");

        invokeMethodWithParams(map, "resize", 0);
    }

    /**
     * Test the postcondition of the resize method of the {@link IdentityHashMap} in case
     * of normal behaviour.
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

        invokeMethodWithParams(map, "resize", 0);

        // Assert that no other fields are assgined a value that "trheshold" and "table",
        // validating the JML clause:
        //     \assignable
        //         threshold table.
        assertAssignableClause(map, "resize", new Integer[]{0}, new String[]{"threshold", "table"}, new int[0]);

        // TODO: more assertions here ....
    }

    @Test
    public void testEqualsPostcondition()
            throws InvocationTargetException, NoSuchMethodException, IllegalAccessException, NoSuchFieldException {
        final IdentityHashMap<String, String> map2 = new IdentityHashMap<>();
        // TODO

        // Test if the equals method is really pure
        assertIsPureMethod(map, "equals", map2);
    }

    @Test
    public void testHashCodePostcondition()
            throws InvocationTargetException, NoSuchMethodException, IllegalAccessException, NoSuchFieldException {
        // TODO

        // Test if the hash method is really pure
        assertIsPureMethod(map, "hashCode");
    }

    @Test
    public void testClonePostcondition()
            throws InvocationTargetException, NoSuchMethodException, IllegalAccessException, NoSuchFieldException {
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
     * @throws InvocationTargetException
     * @throws NoSuchMethodException
     */
    private void assertContainsKeyPostConditionFound(IdentityHashMap<Object, Object> map)
            throws NoSuchFieldException, IllegalAccessException, InvocationTargetException, NoSuchMethodException {
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
     * @throws InvocationTargetException
     * @throws NoSuchMethodException
     */
    private void assertContainsKeyPostConditionNotFound(IdentityHashMap<Object, Object> map)
            throws NoSuchFieldException, IllegalAccessException, InvocationTargetException, NoSuchMethodException {
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
     * @throws InvocationTargetException
     * @throws NoSuchMethodException
     */
    private void assertContainsValuePostConditionFound(IdentityHashMap<Object, Object> map)
            throws NoSuchFieldException, IllegalAccessException, InvocationTargetException, NoSuchMethodException {
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
     * @throws InvocationTargetException
     * @throws NoSuchMethodException
     */
    private void assertContainsValuePostConditionNotFound(IdentityHashMap<Object, Object> map)
            throws NoSuchFieldException, IllegalAccessException, InvocationTargetException, NoSuchMethodException {
        final String key = "aKey";
        final String value = "aValue";
        map.put(key, "aValue");
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
     * @throws InvocationTargetException
     * @throws NoSuchMethodException
     */
    private void assertGetPostConditionForNonNullResult(IdentityHashMap<Object, Object> map)
            throws NoSuchFieldException, IllegalAccessException, InvocationTargetException, NoSuchMethodException {
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

        // Test if the get method is really pure
        assertIsPureMethod(map, "get", key);
    }

    /**
     * Checks if the postcondition for the get method of the {@link IdentityHashMap} holds
     * when a {@code null} value is found and returned as a result.
     *
     * @param map the map to call the get method on
     * @throws NoSuchFieldException
     * @throws IllegalAccessException
     * @throws InvocationTargetException
     * @throws NoSuchMethodException
     */
    private void assertGetPostConditionForNullResult(IdentityHashMap<Object, Object> map)
            throws NoSuchFieldException, IllegalAccessException, InvocationTargetException, NoSuchMethodException {
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
     * @throws InvocationTargetException
     * @throws NoSuchMethodException
     */
    private void assertGetPostConditionKeyNotFound(IdentityHashMap<Object, Object> map)
            throws NoSuchFieldException, IllegalAccessException, InvocationTargetException, NoSuchMethodException {
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
     * @throws InvocationTargetException
     * @throws NoSuchMethodException
     */
    private void assertGetPostConditionValueNull(IdentityHashMap<Object, Object> map)
            throws NoSuchFieldException, IllegalAccessException, InvocationTargetException, NoSuchMethodException {
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

        // Test if the nextKeyIndex method is really pure
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
     * @throws InvocationTargetException
     * @throws NoSuchMethodException
     * @throws IllegalAccessException
     * @throws NoSuchFieldException
     */
    private void assertAssignableNothingClause(IdentityHashMap<Object, Object> map, String methodName, Object[] params)
            throws InvocationTargetException, NoSuchMethodException, IllegalAccessException, NoSuchFieldException {
        this.assertAssignableClause(map, methodName, params, new String[0], new int[0]);
    }

    /**
     * Asserts that fields and/or parameters that are not assignable according to the JML
     * specification, do not get assigned a new value during the invokation of the method
     * under analysis.
     * </P>
     * Example: the JML specification clause {@code assignable threshold, table;} for the
     * method under test {@code init} would be testable by the following call to this method:
     * {@code assertAssignableClause(aMap, "init", new Integer[]{1024}, new String[]{"threshold", "table"}, new int[0]);}
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
     * @throws InvocationTargetException
     * @throws NoSuchMethodException
     */
    private void assertAssignableClause(IdentityHashMap<Object, Object> map, String methodName, Object[] params,
                                        String[] assignableFieldNames, int[] assignableParamIndices)
            throws NoSuchFieldException, IllegalAccessException, InvocationTargetException, NoSuchMethodException {

        // Collect the fields in the IdentityHashMap: fields, their names, and their
        // values before invoking the method under test.
        final Field[] fields = map.getClass().getDeclaredFields();
        final String[] fieldNames = new String[fields.length];
        final Object[] oldFieldValues = new Object[fields.length];
        for (int i = 0; i < fields.length; i++) {
            fieldNames[i] = fields[i].getName();
            oldFieldValues[i] = getValueByFieldName(map, fieldNames[i]);
        }

        // Collect the actual parameters passed to the method under test: their values
        // before invoking the method.
        final Object[] oldParamValues = new Object[params.length];
        for (int i = 0; i < params.length; i++) {
            oldParamValues[i] = params[i];
        }

        // Now, invoke the method
        invokeMethodWithParams(map, methodName, params);

        // Check if the fields have not been unexpectedly assigned a value. Compare
        // the old value with the current value.
        for (int i = 0; i < fieldNames.length; i++) {
            // Skip assignable fields for equality check
            if (!Arrays.asList(assignableFieldNames).contains(fieldNames[i])) {
                assertThat(getValueByFieldName(map, fieldNames[i]), is(oldFieldValues[i]));
            }
        }

        // Check that the parameters have not been unexpectedly assigned a value. Compare
        // the old value with the current value.
        for (int i = 0; i < params.length; i++) {
            // Skip assignable parameters for equality check
            if (!Arrays.asList(assignableParamIndices).contains(i)) {
                assertThat(params[i], is(oldParamValues[i]));
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
            throws NoSuchFieldException, IllegalAccessException, InvocationTargetException, NoSuchMethodException {
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
        final int oldSize = (int) getValueByFieldName(map, "size");
        invokeMethodWithParams(map, "init", initCapacity);
        // Assert that the JML postcodition of the init method holds:
        //   ensures
        //     threshold == ((\bigint)2 * initCapacity) / (\bigint)3 &&
        //     table.length == (\bigint)2 * initCapacity &&
        //     \old(size) == size;
        assertThat((int) getValueByFieldName(map, "threshold"), is((initCapacity * 2) / 3));
        assertThat(((Object[]) getValueByFieldName(map, "table")).length, is(initCapacity * 2));
        assertThat((int) getValueByFieldName(map, "size"), is(oldSize));

        // Assert that no other fields are assgined a value that "trheshold" and "table",
        // validating the JML clause:
        //     \assignable
        //         threshold table.
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
