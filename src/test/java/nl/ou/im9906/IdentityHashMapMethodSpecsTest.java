package nl.ou.im9906;

import org.junit.Before;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.ExpectedException;

import java.lang.reflect.InvocationTargetException;
import java.util.IdentityHashMap;
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
            throws NoSuchMethodException, InvocationTargetException, IllegalAccessException, NoSuchFieldException {
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
    public void testInitPostConditions()
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
        assertIsPure(map, "size");
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
        assertIsPure(map, "isEmpty");
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
        assertIsPure(map, "hash", new Object(), 32);
    }

    @Test
    public void testNextKeyIndexPostcondition()
            throws InvocationTargetException, NoSuchMethodException, IllegalAccessException, NoSuchFieldException {
        // TODO

        // Test if the hash method is really pure
        assertIsPure(map, "nextKeyIndex", 0, 2);
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
    private void assertIsPure(IdentityHashMap<Object, Object> map, String methodName, Object... params)
            throws NoSuchFieldException, IllegalAccessException, InvocationTargetException, NoSuchMethodException {
        final int oldSize = (int) getValueByFieldName(map, "size");
        final int oldThreshold = (int) getValueByFieldName(map, "threshold");
        final int oldModCount = (int) getValueByFieldName(map, "modCount");
        final Object[] oldTable = (Object[]) getValueByFieldName(map, "table");
        final Set<Entry<?, ?>> oldEntrySet = (Set<Entry<?, ?>>) getValueByFieldName(map, "entrySet");

        invokeMethodWithParams(map, methodName, params);

        assertThat((int) getValueByFieldName(map, "size"), is(oldSize));
        assertThat((int) getValueByFieldName(map, "threshold"), is(oldThreshold));
        assertThat((int) getValueByFieldName(map, "modCount"), is(oldModCount));
        assertThat((Object[]) getValueByFieldName(map, "table"), is(oldTable));
        assertThat((Set<Entry<?, ?>>) getValueByFieldName(map, "entrySet"), is(oldEntrySet));
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
        // JML postcodition of the init method:
        //   ensures
        //     threshold == ((\bigint)2 * initCapacity) / (\bigint)3 &&
        //     table.length == (\bigint)2 * initCapacity &&
        //     \old(size) == size;
        assertThat((int) getValueByFieldName(map, "threshold"), is((initCapacity * 2) / 3));
        assertThat(((Object[]) getValueByFieldName(map, "table")).length, is(initCapacity * 2));
        assertThat((int) getValueByFieldName(map, "size"), is(oldSize));
    }

}
