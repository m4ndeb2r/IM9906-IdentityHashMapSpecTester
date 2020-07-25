package nl.ou.im9906;

import org.hamcrest.Matchers;
import org.junit.Before;
import org.junit.Test;

import java.lang.reflect.InvocationTargetException;
import java.math.BigInteger;
import java.util.IdentityHashMap;

import static nl.ou.im9906.ClassInvariantTestHelper.assertClassInvariants;
import static nl.ou.im9906.MethodTestHelper.assertIsPureMethod;
import static nl.ou.im9906.ReflectionUtils.getValueByFieldName;
import static nl.ou.im9906.ReflectionUtils.invokeMethodWithParams;
import static nl.ou.im9906.ReflectionUtils.isPowerOfTwo;
import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.Matchers.greaterThan;
import static org.hamcrest.Matchers.greaterThanOrEqualTo;
import static org.hamcrest.Matchers.lessThanOrEqualTo;
import static org.hamcrest.core.Is.is;

/**
 * Tests the JML specifications of the {@link IdentityHashMap#nextKeyIndex(int, int)}
 * method.
 */
public class IdentityHashMapNextKeyIndexTest {

    // The test subject
    private IdentityHashMap<Object, Object> map;

    @Before
    public void setUp() {
        map = new IdentityHashMap<>();
    }

    /**
     * Test the normal behaviour of the {@link IdentityHashMap#nextKeyIndex(int, int)}
     * is a pure method, and if the JML postcondition holds for several cases.
     *
     * @throws NoSuchFieldException      if one or more fields do not exist
     * @throws IllegalAccessException    if one or more field cannot be accessed
     * @throws NoSuchMethodException     if the method to invoke does not exist
     * @throws InvocationTargetException if the method to invoke throws an exception
     * @throws NoSuchClassException      if one of the (inner) classes does not exist
     */
    @Test
    public void testNextKeyIndexPostcondition()
            throws InvocationTargetException, NoSuchMethodException,
            IllegalAccessException, NoSuchFieldException,
            NoSuchClassException {
        final int i = 1 << 29 - 2;
        final int j = 8;
        assertNextKeyIndexNormalBehaviour(i, j);
        assertNextKeyIndexNormalBehaviour(j, j);
        assertNextKeyIndexNormalBehaviour(i, i);
        assertNextKeyIndexNormalBehaviour(j, i);
    }

    /**
     * Checks the postcondition of the nextKeyIndex method, based on two parameters:
     * the current index, and the length of the table array.
     *
     * @param i   the current index
     * @param len the length of the array to find the next index in
     * @throws NoSuchFieldException      if one or more fields do not exist
     * @throws IllegalAccessException    if one or more field cannot be accessed
     * @throws NoSuchMethodException     if the method to invoke does not exist
     * @throws InvocationTargetException if the method to invoke throws an exception
     * @throws NoSuchClassException      if one of the (inner) classes does not exist
     */
    private void assertNextKeyIndexNormalBehaviour(int i, int len)
            throws IllegalAccessException, InvocationTargetException,
            NoSuchMethodException, NoSuchFieldException,
            NoSuchClassException {
        // Test if the class invariants hold (precondition)
        assertClassInvariants(map);

        // Assert that the following method preconditions hold
        //   requires
        //     MAXIMUM_CAPACITY == 1 << 29 &&
        //     i >= 0 &&
        //     i + (\bigint)2 <= MAXIMUM_CAPACITY &&
        //     i % 2 == 0 &&
        //     len > 2 &&
        //     len <= MAXIMUM_CAPACITY &&
        //     (len & -len) == len;
        final int maxCapacity = (int) getValueByFieldName(map, "MAXIMUM_CAPACITY");
        assertThat(i, greaterThanOrEqualTo(0));
        assertThat(i, lessThanOrEqualTo(Integer.MAX_VALUE));
        assertThat(i % 2, is(0));
        assertThat(len, greaterThan(2));
        assertThat(len, lessThanOrEqualTo(maxCapacity));
        assertThat(isPowerOfTwo(len), is(true));

        // Invoke the method
        final int result = (int) invokeMethodWithParams(map, "nextKeyIndex", i, len);

        // Assert that the following postcondition holds:
        //   ensures
        //     \result < len &&
        //     \result >= 0 &&
        //     \result % (\bigint)2 == 0 &&
        //     i + (\bigint)2 < len ==> \result == i + (\bigint)2 &&
        //     i + (\bigint)2 >= len ==> \result == 0;
        assertThat(result, Matchers.lessThan(len));
        assertThat(result, greaterThanOrEqualTo(0));
        assertThat(result % 2, is(0));
        final BigInteger iBigAddTwo = BigInteger.valueOf((long) i).add(BigInteger.valueOf(2));
        final BigInteger lenBig = BigInteger.valueOf(len);
        if (iBigAddTwo.compareTo(lenBig) < 0) assertThat(result, is(i + 2));
        if (iBigAddTwo.compareTo(lenBig) >= 0) assertThat(result, is(0));

        // Test if the class invariants hold (postcondition)
        assertClassInvariants(map);

        // Test if the nextKeyIndex method is pure
        assertIsPureMethod(map, "nextKeyIndex", i, len);
    }

}
