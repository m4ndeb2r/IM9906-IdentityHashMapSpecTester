package nl.ou.im9906;

import org.junit.Before;
import org.junit.Ignore;
import org.junit.Test;

import java.lang.reflect.InvocationTargetException;
import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.Map;

import static nl.ou.im9906.ClassInvariantTestHelper.assertClassInvariants;
import static nl.ou.im9906.MethodTestHelper.assertIsPureMethod;
import static nl.ou.im9906.ReflectionUtils.getValueByFieldName;
import static nl.ou.im9906.ReflectionUtils.invokeMethodWithParams;
import static nl.ou.im9906.ReflectionUtils.isPowerOfTwo;
import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.Matchers.greaterThanOrEqualTo;
import static org.hamcrest.Matchers.lessThan;
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
     * @throws NoSuchFieldException      if one or more fields do not exist
     * @throws IllegalAccessException    if one or more field cannot be accessed
     * @throws NoSuchMethodException     if the method to invoke does not exist
     * @throws NoSuchClassException      if one of the (inner) classes does not exist
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
     * This test exposes an overflow error in the capacity method. When the capacity method is invoked
     * with an expectedMaxSize greater than MAXIMUM_CAPACITY, is should return a capacity of MAXIMUM_CAPACITY.
     * However, due to an overflow error in {@link IdentityHashMap#capacity(int)}, this is not always the case.
     * When invoke it with an expectedMaxSize of 1431655768, for example, we would expect it to return
     * MAXIMUM_CAPACITY. Instead, it returns 4.
     *
     * @throws NoSuchFieldException
     * @throws IllegalAccessException
     */
    @Test
    public void testCapacityOverflow()
            throws NoSuchMethodException, IllegalAccessException,
            NoSuchFieldException, NoSuchClassException, InvocationTargetException {
        // Test if the class invariants hold (precondition)
        assertClassInvariants(map);

        final int max = (int) getValueByFieldName(map, "MAXIMUM_CAPACITY");
        final int capacity = (int) invokeMethodWithParams(map, "capacity", 1431655768);
        // assertThat(capacity, is(max)); // FAILS because of overflow
        assertThat(capacity, is(4)); // This exposes the output is erroneous

        // Test if the class invariants hold (postcondition)
        assertClassInvariants(map);
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
     * @throws NoSuchFieldException      if one or more fields do not exist
     * @throws IllegalAccessException    if one or more field cannot be accessed
     * @throws NoSuchMethodException     if the method to invoke does not exist
     * @throws NoSuchClassException      if one of the (inner) classes does not exist
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
     * @throws NoSuchFieldException      if one or more fields do not exist
     * @throws IllegalAccessException    if one or more field cannot be accessed
     * @throws NoSuchMethodException     if the method to invoke does not exist
     * @throws NoSuchClassException      if one of the (inner) classes does not exist
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

    /*************************************************************************************************
     * Below are a number of tests to confirm our hypothesis that the IdentityHashMap's capacity
     * method contains a bug. When an expectedMaxValue in the range between 1431655765 and 1610612736
     * is passed, the method returns an unexpected value. The expected value is MAXIMUM_CAPACITY.
     *************************************************************************************************/

    @Test
    public void testOverflowOfThreeTimesExpectedMaxSizeDividedByTwo() {
        int count = 0;
        for (int expectedMaxSize = 1431655765; expectedMaxSize < Integer.MAX_VALUE; expectedMaxSize++) {
            int minCapacity = (3 * expectedMaxSize) / 2;
            if (minCapacity < 0) {
                count++;
                System.out.println(String.format("minCapacity is %d when expectedMaxSize is %d.", minCapacity, expectedMaxSize));
            }
        }
        assertThat(count, is(0));
        System.out.println(String.format("Number of occurrences: %d.", count));
    }

    @Test
    public void testOverflowOfExpectedMaxSizeDividedByTwoTimesThree() {
        int count = 0;
        for (int expectedMaxSize = 1431655766; expectedMaxSize < Integer.MAX_VALUE; expectedMaxSize++) {
            int minCapacity = expectedMaxSize % 2 + (expectedMaxSize / 2) * 3; // Improved calculation
            if (minCapacity >= 0) {
                count++;
                System.out.println(String.format("minCapacity is %d when expectedMaxSize is %d.", minCapacity, expectedMaxSize));
            }
        }
        assertThat(count, is(0));
        System.out.println(String.format("Number of occurrences: %d.", count));
    }

    @Test
    @Ignore
    public void printTest() throws IllegalAccessException, NoSuchMethodException, InvocationTargetException {
        final Map<Integer, Integer[]> categories = new HashMap<>();

        int expectedMaxSize = 1431655760;
        while (expectedMaxSize < Integer.MAX_VALUE || expectedMaxSize < 0) {
            int capacity = (int) invokeMethodWithParams(map, "capacity", expectedMaxSize);
            if (capacity < 536870912) {
                if (categories.get(capacity) == null) {
                    categories.put(capacity, new Integer[]{expectedMaxSize, expectedMaxSize});
                }
                if (expectedMaxSize < categories.get(capacity)[0]) {
                    categories.get(capacity)[0] = expectedMaxSize;
                }
                if (expectedMaxSize > categories.get(capacity)[1]) {
                    categories.get(capacity)[1] = expectedMaxSize;
                }
            }
            expectedMaxSize += 1;
        }
        for (Integer key : categories.keySet()) {
            final Integer[] range = categories.get(key);
            System.out.println(String.format("%d: [%d .. %d]", key, range[0], range[1]));
        }
    }

    private static final int MAXIMUM_CAPACITY = 1 << 29;
    private static final int MINIMUM_CAPACITY = 4;
    private static final int START_EXPECTED_MAX_VAL = (Integer.MAX_VALUE / 3) * 2 + 1;
    private static final int END_EXPECTED_MAX_VAL = Integer.MAX_VALUE;
    private static final int OVERFLOW_THRESHOLD = 1610612737;

    /**
     * This tests an alternative way to calculate (expectedMaxSize * 3) / 2
     */
    @Test
    public void testCalculationImprovement() {
        // Both the original and improved calculations should result in the same value
        // when type is long. Meaning both calculations are mathematically similar.
        for (long i = START_EXPECTED_MAX_VAL; i < OVERFLOW_THRESHOLD; i++) {
            final long original = (i * 3) / 2;
            final long improved = i % 2 + (i / 2) * 3;
            assertThat(original, is(improved)); // <-- expecting SUCCESS (no overflow, calculations are similar)
        }

        // When type is int, both calculations overflow, but the original outcome is
        // larger than zero, and therefore goes unnoticed by the original capacity()
        // method. The improved calculation's outcome is always < 0 when an overflow
        // occurs, and will therefore not go unnoticed.
        for (int i = START_EXPECTED_MAX_VAL; i < OVERFLOW_THRESHOLD; i++) {
            final int original = (i * 3) / 2;
            final int improved = i % 2 + (i / 2) * 3;

            // Overflow goes unnoticed in the original
            assertThat(original, greaterThanOrEqualTo(0));
            assertThat(improved > 0 || improved < MAXIMUM_CAPACITY, is(true));

            // Overflow will be noticed in the improved version
            assertThat(improved > MAXIMUM_CAPACITY || improved < 0, is(true));
        }
    }

    /**
     * This test shows that the capacityOriginal method (a copy of the method
     * {@link IdentityHashMap#capacity(int)} of the JDK7 Collections Framework does not
     * detect an overflow when the input parameter expectedMaxSize contains a value in
     * the range [START_EXPECTED_MAX_VAL .. OVERFLOW_THRESHOLD - 1]. It will return a
     * value > 0, but < {@link IdentityHashMap#MAXIMUM_CAPACITY}. This is a bug.
     * </p>
     * When the input parameter expectedMaxSize contains a value larger than or equal to
     * OVERFLOW_THRESHOLD, the overflow will be detected, and the method returns the value
     * MAXIMUM_CAPACITY, which is correct.
     */
    @Test
    public void testCapacityOriginal() {
        for (int i = START_EXPECTED_MAX_VAL; i < END_EXPECTED_MAX_VAL; i++) {
            final int capacity = capacityOriginal(i);
            if (i < OVERFLOW_THRESHOLD) {
                // If the overflow is not detected ...
                // This contradicts (!) the specs of the method
                assertThat(capacity, lessThan(MAXIMUM_CAPACITY));
            } else {
                // If the overflow is detected ...
                // This conforms to the specs of the method
                assertThat(capacity, is(MAXIMUM_CAPACITY));
            }
        }
    }

    /**
     * This test shows that the capacityImproved method (an improved version of the method
     * {@link IdentityHashMap#capacity(int)} of the JDK7 Collections Framework does detect
     * an overflow, and, in that case, returns MAXIMUM_CAPACITY, like it is supposed to do.
     * This resolves the bug in the original method.
     */
    @Test
    public void testCapacityImproved() {
        for (int i = START_EXPECTED_MAX_VAL; i < END_EXPECTED_MAX_VAL; i++) {
            final int capacity = capacityImproved(i);
            // If the overflow is detected by capacity, this should return MAXIMUM_CAPACITY.
            // If a value > MAXIMUM_CAPACITY is passed, this should also return MAXIMUM_CAPACITY.
            assertThat(capacity, is(MAXIMUM_CAPACITY));
        }

        // Check if there are no differences with the original method, as far as the not-so-large
        // expectedMaxSize values are concerned.
        for (int i = 1; i < MAXIMUM_CAPACITY; i *= 3) {
            assertThat(capacityImproved(i - 1), is(capacityOriginal(i - 1)));
        }
    }

    /**
     * This test shows that the capacityJava9 method does detect an overflow, and, in that case,
     * returns MAXIMUM_CAPACITY, like it is supposed to do. This means the bug in the JDK7 and
     * JDK8 version is resolved.
     */
    @Test
    public void testCapacityJava9() {
        for (int i = START_EXPECTED_MAX_VAL; i < END_EXPECTED_MAX_VAL; i++) {
            final int capacity = capacityJava9(i);
            // If the overflow is detected by capacity, this should return MAXIMUM_CAPACITY.
            // If a value > MAXIMUM_CAPACITY is passed, this should also return MAXIMUM_CAPACITY.
            assertThat(capacity, is(MAXIMUM_CAPACITY));
        }

        // Check if there are no differences with the original JDK7 method, as far as the not-so-large
        // expectedMaxSize values are concerned.
        for (int i = 1; i < MAXIMUM_CAPACITY; i *= 3) {
            assertThat(capacityJava9(i - 1), is(capacityOriginal(i - 1)));
        }
    }

    // This is a copy of the original Java JDK7 capacity method
    private int capacityOriginal(int expectedMaxSize) {
        int minCapacity = (3 * expectedMaxSize) / 2;
        int result;
        if (minCapacity > MAXIMUM_CAPACITY || minCapacity < 0) {
            result = MAXIMUM_CAPACITY;
        } else {
            result = MINIMUM_CAPACITY;
            while (result < minCapacity)
                result <<= 1;
        }
        return result;
    }

    // This is an improved version of the original Java JDK7 capacity method
    private int capacityImproved(int expectedMaxSize) {
        int minCapacity = expectedMaxSize % 2 + (expectedMaxSize / 2) * 3; // Improved calculation
        int result;
        if (minCapacity > MAXIMUM_CAPACITY || minCapacity < 0) {
            result = MAXIMUM_CAPACITY;
        } else {
            result = MINIMUM_CAPACITY;
            while (result < minCapacity)
                result <<= 1;
        }
        return result;
    }

    // The Java 9 version of capacity
    private int capacityJava9(int expectedMaxSize) {
        return
                (expectedMaxSize > MAXIMUM_CAPACITY / 3) ? MAXIMUM_CAPACITY :
                        (expectedMaxSize <= 2 * MINIMUM_CAPACITY / 3) ? MINIMUM_CAPACITY :
                                Integer.highestOneBit(expectedMaxSize + (expectedMaxSize << 1));
    }

}
