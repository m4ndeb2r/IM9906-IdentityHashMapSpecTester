package nl.ou.im9906;

import org.junit.Before;
import org.junit.Test;

import java.lang.reflect.InvocationTargetException;
import java.util.IdentityHashMap;

import static nl.ou.im9906.ClassInvariantTestHelper.assertClassInvariants;
import static nl.ou.im9906.MethodTestHelper.assertIsPureMethod;
import static nl.ou.im9906.ReflectionUtils.getValueByFieldName;
import static nl.ou.im9906.ReflectionUtils.invokeMethodWithParams;
import static nl.ou.im9906.ReflectionUtils.isPowerOfTwo;
import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.core.Is.is;

/**
 * Tests the JML specifications of the {@link IdentityHashMap#capacity(int)} method.
 */
public class IdentityHashMapCapacityTest {

    private IdentityHashMap<Object, Object> map;

    @Before
    public void setUp() {
        // Create an instance of the IdentityHashMap
        map = new IdentityHashMap<>();
    }

    /**
     * Tests the {@link IdentityHashMap#capacity(int)} method's normal behaviour in
     * case of 3 * expectedMaxSize / 2 < 0 situation.
     * <p/>
     * The JML specification to test:
     * <pre>
     *   requires
     *     MAXIMUM_CAPACITY == 536870912 &&
     *     ((3 * expectedMaxSize) / 2) < 0;
     *   ensures
     *     \result == MAXIMUM_CAPACITY;
     * </pre>
     *
     * @throws NoSuchFieldException      if one or more fields do not exist
     * @throws IllegalAccessException    if one or more field cannot be accessed
     * @throws NoSuchMethodException     if the method to invoke does not exist
     * @throws NoSuchClassException      if one of the (inner) classes does not exist
     * @throws InvocationTargetException if an exception occured during the invocation of the capacity method
     */
    @Test
    public void testCapacityNormalBehaviourLessThanZero()
            throws NoSuchMethodException, IllegalAccessException,
            NoSuchFieldException, NoSuchClassException, InvocationTargetException {
        // Test if the class invariants hold (precondition)
        assertClassInvariants(map);

        final int capacity = (int) invokeMethodWithParams(map, "capacity", -1);
        final int max = (int) getValueByFieldName(map, "MAXIMUM_CAPACITY");
        assertThat(capacity, is(max));

        // Test if the class invariants hold (postcondition)
        assertClassInvariants(map);

        // Assert that the method is pure.
        assertIsPureMethod(map, "capacity", -1);
    }

    /**
     * Tests the {@link IdentityHashMap#capacity(int)} method's normal behaviour in
     * case of 3 * expectedMaxSize / 2 > MAXIMUM_CAPACITY situation.
     * <p/>
     * The JML specification to test:
     * <pre>
     *   requires
     *     MAXIMUM_CAPACITY == 536870912 &&
     *     ((3 * expectedMaxSize) / 2) > MAXIMUM_CAPACITY;
     *   ensures
     *     \result == MAXIMUM_CAPACITY;
     * </pre>
     *
     * @throws NoSuchFieldException   if one or more fields do not exist
     * @throws IllegalAccessException if one or more field cannot be accessed
     * @throws NoSuchMethodException  if the method to invoke does not exist
     * @throws NoSuchClassException   if one of the (inner) classes does not exist
     * @throws InvocationTargetException if an exception occured during the invocation of the capacity method
     */
    @Test
    public void testCapacityNormalBehaviourGreaterThanMax()
            throws NoSuchMethodException, IllegalAccessException,
            NoSuchFieldException, NoSuchClassException, InvocationTargetException {
        // Test if the class invariants hold (precondition)
        assertClassInvariants(map);

        final int max = (int) getValueByFieldName(map, "MAXIMUM_CAPACITY");
        final int capacity = (int) invokeMethodWithParams(map, "capacity", max + 1);
        assertThat(capacity, is(max));

        // Test if the class invariants hold (postcondition)
        assertClassInvariants(map);

        // Assert that the method is pure.
        assertIsPureMethod(map, "capacity", max + 1);
    }

    /**
     * Tests the {@link IdentityHashMap#capacity(int)} method's normal behaviour in
     * case of 3 * expectedMaxSize / 2 valid (no adjustment needed) situation.
     * <p/>
     * The JML specification to test:
     * <pre>
     *   requires
     *     MINIMUM_CAPACITY == 4 &&
     *     MAXIMUM_CAPACITY == 536870912 &&
     *     ((3 * expectedMaxSize) / 2) >= MINIMUM_CAPACITY &&
     *     ((3 * expectedMaxSize) / 2) <= MAXIMUM_CAPACITY;
     *   ensures
     *     \result >= ((3 * expectedMaxSize) / 2) &&
     *     \result < (3 * expectedMaxSize) &&
     *     (\exists \bigint i;
     *         0 <= i < \result;
     *         \dl_pow(2,i) == \result);
     * </pre>
     *
     * @throws NoSuchFieldException   if one or more fields do not exist
     * @throws IllegalAccessException if one or more field cannot be accessed
     * @throws NoSuchMethodException  if the method to invoke does not exist
     * @throws NoSuchClassException   if one of the (inner) classes does not exist
     * @throws InvocationTargetException if an exception occured during the invocation of the capacity method
     */
    @Test
    public void testCapacityNormalBehaviourValid()
            throws NoSuchMethodException, IllegalAccessException,
            NoSuchFieldException, NoSuchClassException, InvocationTargetException {
        // Test if the class invariants hold (precondition)
        assertClassInvariants(map);

        final int min = (int) getValueByFieldName(map, "MINIMUM_CAPACITY");
        final int max = (int) getValueByFieldName(map, "MAXIMUM_CAPACITY");

        int capacity = (int) invokeMethodWithParams(map, "capacity", 3);
        assertThat(capacity, is(4));
        capacity = (int) invokeMethodWithParams(map, "capacity", 8);
        assertThat(capacity, is(16));
        capacity = (int) invokeMethodWithParams(map, "capacity", 20);
        assertThat(capacity, is(32));
        capacity = (int) invokeMethodWithParams(map, "capacity", max / 2);
        assertThat(capacity, is(max));

        // Now run capacity with some pseudo-random inputs, test if the result is always a
        // power of 2, if the class invariant still holds, and if the method is pure with
        // the input.
        for (int i = min; i < max / 2; i = i * 3 - 1) {
            capacity = (int) invokeMethodWithParams(map, "capacity", i);
            // Is result a power of 2?
            assertThat(isPowerOfTwo(capacity), is(true));
            // Test if the class invariants hold (postcondition)
            assertClassInvariants(map);
            // Assert that the method is pure.
            assertIsPureMethod(map, "capacity", i);
        }
    }

    /**
     * Tests the {@link IdentityHashMap#capacity(int)} method's normal behaviour in
     * case of 3 * expectedMaxSize / 2 valid (no adjustment needed) situation.
     * <p/>
     * The JML specification to test:
     * <pre>
     *   requires
     *     MINIMUM_CAPACITY == 4 &&
     *     ((3 * expectedMaxSize) / 2) >= 0 &&
     *     ((3 * expectedMaxSize) / 2) < MINIMUM_CAPACITY;
     *   ensures
     *     \result < MINIMUM_CAPACITY * 2 &&
     *     \result >= MINIMUM_CAPACITY &&
     *     (\exists \bigint i;
     *         0 <= i < \result;
     *         \dl_pow(2,i) == \result);
     * </pre>
     *
     * @throws NoSuchFieldException   if one or more fields do not exist
     * @throws IllegalAccessException if one or more field cannot be accessed
     * @throws NoSuchMethodException  if the method to invoke does not exist
     * @throws NoSuchClassException   if one of the (inner) classes does not exist
     * @throws InvocationTargetException if an exception occured during the invocation of the capacity method
     */
    @Test
    public void testCapacityNormalBehaviourLessThanMin()
            throws NoSuchMethodException, IllegalAccessException,
            NoSuchFieldException, NoSuchClassException, InvocationTargetException {
        // Test if the class invariants hold (precondition)
        assertClassInvariants(map);

        final int min = (int) getValueByFieldName(map, "MINIMUM_CAPACITY");

        int capacity = (int) invokeMethodWithParams(map, "capacity", 1);
        assertThat(capacity, is(min));
        capacity = (int) invokeMethodWithParams(map, "capacity", 2);
        assertThat(capacity, is(min));

        // Test if the class invariants hold (postcondition)
        assertClassInvariants(map);

        // Assert that the method is pure.
        assertIsPureMethod(map, "capacity", 8);
    }

}
