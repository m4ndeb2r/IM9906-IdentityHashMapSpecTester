package nl.ou.im9906;

import org.junit.Before;
import org.junit.Test;

import java.lang.reflect.InvocationTargetException;
import java.util.IdentityHashMap;

import static nl.ou.im9906.ClassInvariantTestHelper.assertClassInvariants;
import static nl.ou.im9906.MethodTestHelper.assertAssignableClause;
import static nl.ou.im9906.ReflectionUtils.getValueByFieldName;
import static nl.ou.im9906.ReflectionUtils.setValueByFieldName;
import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.core.Is.is;

/**
 * Tests the JML specifications of the {@link IdentityHashMap#resize(int)} method.
 */
public class IdentityHashMapResizeTest {

    // The test subject
    private IdentityHashMap<Object, Object> map;

    @Before
    public void setUp() {
        map = new IdentityHashMap<>();
    }

    // TODO: test exceptional behaviour (IllegalStatException). Problem: memory issues...

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
     * Also tests the assignable clause:
     * <pre>
     *     \assignable
     *        threshold, table
     * </pre>
     * Note: skipping tests with large tables (MAXIMUM_CAPACITY) due to max memory errors.
     *
     * @throws NoSuchFieldException      if one or more fields do not exist
     * @throws IllegalAccessException    if one or more field cannot be accessed
     * @throws NoSuchMethodException     if the method to invoke does not exist
     * @throws InvocationTargetException if the method to invoke throws an exception
     * @throws NoSuchClassException      if one of the (inner) classes does not exist
     */
    @Test
    public void testResizeNormalBehavior()
            throws NoSuchFieldException, IllegalAccessException,
            InvocationTargetException, NoSuchMethodException,
            NoSuchClassException {
        final int minCapacity = (int) getValueByFieldName(map, "MINIMUM_CAPACITY");
        final Object[] table = new Object[minCapacity * 2];
        setValueByFieldName(map, "table", table);
        setValueByFieldName(map, "threshold", minCapacity * 2 / 3);

        // Test 3 scenarios
        assertDoubleNewCapacitySmallerThanOldLengthDontResize(map);
        assertDoubleNewCapacityEqualOldLengthDontResize(map);
        assertDoubleNewCapacityGreaterThanOldLengthDoResize(map);
    }

    /**
     * Asserts that:
     * <ol>
     *     <li>the table is not resized if the newCapacity * 2 < oldTable.length</li>
     *     <li>no variable is assigned except threshold and table</li>
     *     <li>all the original elements are still present in the table on the original index</li>
     * </ol>
     *
     * @param map the test subject
     * @throws NoSuchFieldException      if one or more fields do not exist
     * @throws IllegalAccessException    if one or more field cannot be accessed
     * @throws NoSuchMethodException     if the method to invoke does not exist
     * @throws InvocationTargetException if the method to invoke throws an exception
     * @throws NoSuchClassException      if one of the (inner) classes does not exist
     */
    private void assertDoubleNewCapacitySmallerThanOldLengthDontResize(final IdentityHashMap<Object, Object> map)
            throws NoSuchFieldException, IllegalAccessException,
            InvocationTargetException, NoSuchMethodException,
            NoSuchClassException {
        final Object[] oldTable = (Object[]) getValueByFieldName(map, "table");
        final Object[] newTable = resizeAndAssertAssignableClause(map, oldTable.length / 2 - 1);
        assertThat(newTable.length, is(oldTable.length));
        assertKeyAndValuesPresentInSameLocation(oldTable, newTable);
    }

    /**
     * Asserts that:
     * <ol>
     *     <li>the table is not resized if the newCapacity * 2 == oldTable.length</li>
     *     <li>no variable is assigned except threshold and table</li>
     *     <li>all the original elements are still present in the table on the original index</li>
     * </ol>
     *
     * @param map the test subject
     * @throws NoSuchFieldException      if one or more fields do not exist
     * @throws IllegalAccessException    if one or more field cannot be accessed
     * @throws NoSuchMethodException     if the method to invoke does not exist
     * @throws InvocationTargetException if the method to invoke throws an exception
     * @throws NoSuchClassException      if one of the (inner) classes does not exist
     */
    private void assertDoubleNewCapacityEqualOldLengthDontResize(final IdentityHashMap<Object, Object> map)
            throws NoSuchFieldException, IllegalAccessException,
            InvocationTargetException, NoSuchMethodException,
            NoSuchClassException {
        final Object[] oldTable = (Object[]) getValueByFieldName(map, "table");
        final Object[] newTable = resizeAndAssertAssignableClause(map, oldTable.length / 2);
        assertThat(newTable.length, is(oldTable.length));
        assertKeyAndValuesPresentInSameLocation(oldTable, newTable);
    }

    /**
     * Asserts that:
     * <ol>
     *     <li>the table is resized if the newCapacity * 2 > oldTable.length</li>
     *     <li>no variable is assigned except threshold and table</li>
     *     <li>all the original elements are still present in the table on the original index</li>
     * </ol>
     *
     * @param map the test subject
     * @throws NoSuchFieldException      if one or more fields do not exist
     * @throws IllegalAccessException    if one or more field cannot be accessed
     * @throws NoSuchMethodException     if the method to invoke does not exist
     * @throws InvocationTargetException if the method to invoke throws an exception
     * @throws NoSuchClassException      if one of the (inner) classes does not exist
     */
    private void assertDoubleNewCapacityGreaterThanOldLengthDoResize(final IdentityHashMap<Object, Object> map)
            throws NoSuchFieldException, IllegalAccessException,
            InvocationTargetException, NoSuchMethodException,
            NoSuchClassException {
        final Object[] oldTable = (Object[]) getValueByFieldName(map, "table");
        final Object[] newTable = resizeAndAssertAssignableClause(map, oldTable.length);
        assertThat(newTable.length, is(oldTable.length * 2));
        assertKeyAndValuesPresentInSameLocation(oldTable, newTable);
    }

    /**
     * Invokes the resize method of the specified {@link IdentityHashMap}, while
     * checking its JML assignable clause.
     *
     * @param map         the map containing the table to resize
     * @param newCapacity the desired new capacity
     * @return the resulting table
     * @throws NoSuchFieldException      if one or more fields do not exist
     * @throws IllegalAccessException    if one or more field cannot be accessed
     * @throws NoSuchMethodException     if the method to invoke does not exist
     * @throws InvocationTargetException if the method to invoke throws an exception
     * @throws NoSuchClassException      if one of the (inner) classes does not exist
     */
    private Object[] resizeAndAssertAssignableClause(final IdentityHashMap<Object, Object> map, int newCapacity)
            throws NoSuchFieldException, IllegalAccessException,
            InvocationTargetException, NoSuchMethodException,
            NoSuchClassException {
        // Test if the class invariants hold (precondition)
        assertClassInvariants(map);

        // Here, we invoke the resize method with two objectives:
        // 1. actually call it to resize the table if necessary
        // 2. assert that no other fields are assgined a value that "trheshold" and "table",
        //    validating the JML clause:
        //        \assignable
        //           threshold, table.
        assertAssignableClause(
                map,
                "resize",               // actually call the resize method
                new Integer[]{newCapacity},        // newCapacity * 2 == length of \old(table) -> don't resize
                new String[]{"threshold", "table"} // only threshhold and table may be changed
        );

        // Test if the class invariants hold (postcondition)
        assertClassInvariants(map);

        // Return the resulting table
        return (Object[]) getValueByFieldName(map, "table");
    }

    /**
     * Checks if all the elements in {@code oldTable} are present in
     * {@code newTable} and on the same location.
     *
     * @param oldTable the old table
     * @param newTable the new table (resized), that should contain all elements
     *                 that are present in {@code oldTable}, and on the same location.
     */
    private void assertKeyAndValuesPresentInSameLocation(Object[] oldTable, Object[] newTable) {
        for (int i = 0; i < oldTable.length; i++) {
            // Check if all the keys and values are still present in the same location.
            assertThat(oldTable[i] == newTable[i], is(true));
        }
    }

}
