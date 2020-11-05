package nl.ou.im9906;

import org.junit.Before;
import org.junit.Test;

import java.lang.reflect.InvocationTargetException;
import java.util.IdentityHashMap;

import static nl.ou.im9906.ClassInvariantTestHelper.assertClassInvariants;
import static nl.ou.im9906.MethodTestHelper.assertAssignableClause;
import static nl.ou.im9906.MethodTestHelper.assertAssignableNothingClause;
import static nl.ou.im9906.ReflectionUtils.getValueByFieldName;
import static nl.ou.im9906.ReflectionUtils.invokeMethodWithParams;
import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.Matchers.not;
import static org.hamcrest.core.Is.is;

/**
 * Tests the JML specifications of the {@link IdentityHashMap#removeMapping(Object, Object)}
 * method.
 */
public class IdentityHashMapRemoveMappingTest {

    private IdentityHashMap<Object, Object> map;

    @Before
    public void setUp() {
        map = new IdentityHashMap<>();
    }

    /**
     * Tests the normal behaviour the method {@link IdentityHashMap#removeMapping(Object, Object)}
     * when the element exists.
     * <p/>
     * JML to test:
     * <pre>
     *    requires
     *      // The element exists in the table
     *      ((\exists int i;
     *          0 <= i < \old(table.length) - 1 ;
     *          i % 2 == 0 ==> \old(table[i]) == key && \old(table[i + 1]) == value));
     *    assignable
     *      size, table, modCount;
     *    ensures
     *      size == \old(size) - 1 && modCount != \old(modCount) && \result == true &&
     * 
     *      // The to-be-removed element is no longer present
     *      !((\exists int i;
     *          0 <= i < \old(table.length) - 1 ;
     *          i % 2 == 0 ==> table[i] == key && table[i + 1] == value)) &&
     * 
     *      // All not-to-be-removed elements are still present
     *      (\forall int i;
     *        0 <= i < \old(table.length) - 1 && i % 2 == 0;
     *        \old(table[i]) != key || \old(table[i+1]) != value ==>
     *          (\exists int j;
     *             0 <= j < table.length - 1;
     *             j % 2 == 0 && table[j] == \old(table[i]) && table[j+1] == \old(table[i+1])));
     * </pre>
     * <p>
     * throws NoSuchFieldException      if one or more fields do not exist
     * throws IllegalAccessException    if one or more field cannot be accessed
     * throws NoSuchMethodException     if the method to invoke does not exist
     * throws NoSuchClassException      if one of the (inner) classes does not exist
     * throws InvocationTargetException if an error call using reflection threw an exception
     */
    @Test
    public void testRemoveNormalBehaviourWhenKeyExists()
            throws NoSuchMethodException, IllegalAccessException,
            NoSuchFieldException, NoSuchClassException, InvocationTargetException {

        final String key1 = "Key1";
        final String value1 = "Value1";
        map.put(key1, value1);

        final String key2 = "Key2";
        final String value2 = "Value2";
        map.put(key2, value2);

        final String key3 = "Key3";
        final String value3 = "Value3";
        map.put(key3, value3);

        // Check class invariants (precondition)
        assertClassInvariants(map);

        int oldSize = (int) getValueByFieldName(map, "size");
        int oldModCount = (int) getValueByFieldName(map, "modCount");

        // Remove key1 and check the assignable clause for the remove method
        assertAssignableClauseForRemoveMapping(key1, value1);
        // Assert postcondition
        assertThat(map.size(), is(2));
        assertThat((int) getValueByFieldName(map, "size"), is(oldSize - 1));
        assertThat((int) getValueByFieldName(map, "modCount"), not(is(oldModCount)));
        assertMappingNotInTable(key1, value1);
        assertAllFoundInTable(key2, key3);

        oldSize = (int) getValueByFieldName(map, "size");
        oldModCount = (int) getValueByFieldName(map, "modCount");

        // Remove key2 and check return value
        assertThat((String) invokeMethodWithParams(map, "remove", key2), is(value2));
        // Assert postcondition
        assertThat(map.size(), is(1));
        assertThat((int) getValueByFieldName(map, "size"), is(oldSize - 1));
        assertThat((int) getValueByFieldName(map, "modCount"), not(is(oldModCount)));
        assertMappingNotInTable(key2, value2);
        assertAllFoundInTable(key3);

        // Check class invariants (postcondition)
        assertClassInvariants(map);
    }


    /**
     * Tests the normal behaviour the method {@link IdentityHashMap#removeMapping(Object, Object)}
     * when the element does not exist.
     * <p/>
     * JML to test:
     * <pre>
     *    requires
     *      // The element does not exist in the table
     *      !((\exists int i;
     *          0 <= i < \old(table.length) - 1 ;
     *          i % 2 == 0 ==> table[i] == key && table[i + 1] == value));
     *    assignable
     *      \nothing;
     *    ensures
     *      size == \old(size) && modCount == \old(modCount) && \result == false &&
     *
     *      // All not-to-be-removed elements are still present
     *      (\forall int i;
     *        0 <= i < \old(table.length) - 1 && i % 2 == 0;
     *        \old(table[i]) != key || \old(table[i+1]) != value ==>
     *          (\exists int j;
     *             0 <= j < table.length - 1;
     *             j % 2 == 0 && table[j] == \old(table[i]) && table[j+1] == \old(table[i+1])));
     * </pre>
     * <p>
     * throws NoSuchFieldException      if one or more fields do not exist
     * throws IllegalAccessException    if one or more field cannot be accessed
     * throws NoSuchMethodException     if the method to invoke does not exist
     * throws NoSuchClassException      if one of the (inner) classes does not exist
     * throws InvocationTargetException if an error call using reflection threw an exception
     */
    @Test
    public void testRemoveMappingNormalBehaviourWhenElementDoesNotExist()
            throws NoSuchMethodException, IllegalAccessException,
            NoSuchFieldException, NoSuchClassException,
            InvocationTargetException {
        final String key1 = "Key1";
        map.put(key1, "Value1");
        final String key2 = "Key2";
        map.put(key2, "Value2");
        final String key3 = "Key3";
        map.put(key3, "Value3");

        // Check class invariants (pre-condition)
        assertClassInvariants(map);

        int oldSize = (int) getValueByFieldName(map, "size");
        int oldModCount = (int) getValueByFieldName(map, "modCount");

        // Check the assignable clause: no changes allowed when key does not exist
        assertAssignableNothingClause(map, "removeMapping", new String[]{key1, "unknownValue"});

        // Assert postcondition
        assertThat(map.size(), is(3));
        assertThat((int) getValueByFieldName(map, "size"), is(oldSize));
        assertThat((int) getValueByFieldName(map, "modCount"), is(oldModCount));
        assertThat((Boolean) invokeMethodWithParams(map, "removeMapping", new String[]{key2, "unknownValue"}), is(false));
        assertAllFoundInTable(key1, key2, key3);

        // Check class invariants (post-condition)
        assertClassInvariants(map);
    }

    // Check assignable clause: assignable szie, table, modCount
    private void assertAssignableClauseForRemoveMapping(String key, String value)
            throws NoSuchFieldException, IllegalAccessException,
            NoSuchMethodException {
        assertAssignableClause(
                map,
                "removeMapping",
                new String[]{key, value},
                new String[]{"size", "table", "modCount"}
        );
    }

    // Check that the specified key is not present in the table
    private void assertMappingNotInTable(String key, String value)
            throws NoSuchFieldException, IllegalAccessException,
            NoSuchMethodException {
        final Object[] table = (Object[]) getValueByFieldName(map, "table");
        for (int i = 0; i < table.length; i += 2) {
            assertThat(table[i] == key && table[i + 1] == value, is(false));
        }
    }

    // Check that the specified key is not present in the table
    private void assertAllFoundInTable(String... keys)
            throws NoSuchFieldException, IllegalAccessException,
            NoSuchMethodException {
        final Object[] table = (Object[]) getValueByFieldName(map, "table");
        for (String key : keys) {
            boolean found = false;
            for (int i = 0; i < table.length; i += 2) {
                if (key == table[i] && map.get(key) == table[i + 1]) {
                    found = true;
                    break;
                }
            }
            assertThat(found, is(true));
        }
    }

}
