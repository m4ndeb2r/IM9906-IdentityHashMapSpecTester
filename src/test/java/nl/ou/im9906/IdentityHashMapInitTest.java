package nl.ou.im9906;

import org.junit.Test;

import java.lang.reflect.InvocationTargetException;
import java.util.IdentityHashMap;

import static nl.ou.im9906.ClassInvariantsAssertions.assertClassInvariants;
import static nl.ou.im9906.MethodAssertions.assertAssignableClause;
import static nl.ou.im9906.TestHelper.getValueByFieldName;
import static nl.ou.im9906.TestHelper.invokeMethodWithParams;
import static nl.ou.im9906.TestHelper.isPowerOfTwo;
import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.Matchers.greaterThanOrEqualTo;
import static org.hamcrest.Matchers.lessThanOrEqualTo;
import static org.hamcrest.core.Is.is;

/**
 * Tests the JML specifications of the {@link IdentityHashMap#init(int)
 * method.
 */
public class IdentityHashMapInitTest {

    // The test subject
    private IdentityHashMap<Object, Object> map;

    /**
     * Tests the normal behaviour of the method {@link IdentityHashMap#init(int)}.
     * Pre-conditions are: the parameter initCapacity must be a power of 2, and must
     * be a value between MINIMUM_CAPACITY and MAXIMUM_CAPACITY, and size must be 0.
     * Postconditions are: threshold must have a value (2 * initCapacity) / 3, the
     * lenght of the table array must be 2 * initCapacity, and the size must be
     * unchanged.
     * </p>
     * Furthermore, it is tested if the class invariant holds as a precondition and
     * as a postcondition of the method call.
     *
     * @throws NoSuchFieldException      if one or more fields do not exist
     * @throws IllegalAccessException    if one or more field cannot be accessed
     * @throws NoSuchMethodException     if the method to invoke does not exist
     * @throws InvocationTargetException if the method to invoke throws an exception
     * @throws NoSuchClassException      if one of the (inner) classes does not exist
     */
    @Test
    public void testInitNormalBehavior()
            throws NoSuchMethodException, IllegalAccessException, InvocationTargetException,
            NoSuchFieldException, NoSuchClassException {
        // Small capacity
        map = new IdentityHashMap<>();
        assertInitNormalBehavior((int) getValueByFieldName(map, "MINIMUM_CAPACITY"));

        // Medium capacity
        map = new IdentityHashMap<>();
        assertInitNormalBehavior((int) getValueByFieldName(map, "DEFAULT_CAPACITY"));

        // Large capacity
        map = new IdentityHashMap<>();
        assertInitNormalBehavior(134217728);
    }

    /**
     * Checks the postcondition after invoking the init method of the {@link IdentityHashMap} class.
     *
     * @param initCapacity the actual parameter to pass to the init method
     * @throws NoSuchFieldException      if one or more fields do not exist
     * @throws IllegalAccessException    if one or more field cannot be accessed
     * @throws NoSuchMethodException     if the method to invoke does not exist
     * @throws InvocationTargetException if the method to invoke throws an exception
     * @throws NoSuchClassException      if one of the (inner) classes does not exist
     */
    private void assertInitNormalBehavior(int initCapacity)
            throws NoSuchFieldException, IllegalAccessException, NoSuchMethodException,
            InvocationTargetException, NoSuchClassException {
        // Test if the class invariants hold (precondition)
        assertClassInvariants(map);

        // Assert method precondition
        //   requires
        //     MINIMUM_CAPACITY == 4 && 
        //     MAXIMUM_CAPACITY == 1 << 29 &&
        //     (initCapacity & -initCapacity) == initCapacity &&
        //     initCapacity >= MINIMUM_CAPACITY &&
        //     initCapacity <= MAXIMUM_CAPACITY &&
        //     size == 0;
        assertThat(isPowerOfTwo(initCapacity), is(true));
        assertThat(initCapacity, greaterThanOrEqualTo(4));
        assertThat(initCapacity, lessThanOrEqualTo(1 << 29));

        // Execute the init method
        invokeMethodWithParams(map, "init", initCapacity);

        // Assert that the JML postcondition of the init method holds:
        //   ensures
        //     threshold == ((\bigint)2 * initCapacity) / (\bigint)3 &&
        //     table.length == (\bigint)2 * initCapacity;
        assertThat((int) getValueByFieldName(map, "threshold"), is((initCapacity * 2) / 3));
        assertThat(((Object[]) getValueByFieldName(map, "table")).length, is(initCapacity * 2));

        // Test if the class invariants hold (postcondition)
        assertClassInvariants(map);

        // Assert that no other fields are assigned a value that "threshold" and "table",
        // validating the JML clause:
        //     \assignable
        //         threshold, table.
        assertAssignableClause(map, "init", new Integer[]{initCapacity}, new String[]{"threshold", "table"}, new int[0]);
    }

}
