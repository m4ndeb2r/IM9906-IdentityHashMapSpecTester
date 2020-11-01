package nl.ou.im9906;

import org.hamcrest.Matchers;
import org.junit.Before;
import org.junit.Test;

import java.lang.reflect.InvocationTargetException;
import java.util.IdentityHashMap;
import static nl.ou.im9906.ClassInvariantTestHelper.assertClassInvariants;
import static nl.ou.im9906.MethodTestHelper.assertAssignableClause;
import static nl.ou.im9906.ReflectionUtils.getValueByFieldName;
import static nl.ou.im9906.ReflectionUtils.invokeMethodWithParams;
import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.Matchers.not;
import static org.hamcrest.Matchers.nullValue;
import static org.hamcrest.core.Is.is;

/**
 * Tests the JML specifications of the {@link IdentityHashMap#remove(Object)}
 * method.
 */
public class IdentityHashMapRemoveTest {

    private IdentityHashMap<Object, Object> map;

    @Before
    public void setUp() {
        map = new IdentityHashMap<>();
    }

    /**
     * Tests the normal behaviour the method {@link IdentityHashMap#remove(Object)}
     * when the key to be removed exists.
     * <p/>
     * JML to test:
     * <pre>
     *   assignable
     *     size, table, modCount;
     *   ensures
     *     size == \old(size) - 1 &&
     *     modCount != \old(modCount) &&
     *     (\forall j;
     *       0 <= j < \old(table.length) - 1 && j % 2 == 0;
     *       table[j] == key ==> \result == table[j + 1]);
     * </pre>
     *
     * @throws NoSuchFieldException   if one or more fields do not exist
     * @throws IllegalAccessException if one or more field cannot be accessed
     * @throws NoSuchMethodException  if the method to invoke does not exist
     * @throws NoSuchClassException   if one of the (inner) classes does not exist
     */
    @Test
    public void testRemoveNormalBehaviourWhenKeyExists()
            throws NoSuchMethodException, IllegalAccessException,
            NoSuchFieldException, NoSuchClassException, InvocationTargetException {

        final String key1 = "Key1";
        map.put(key1, "Value1");
        final String key2 = "Key2";
        map.put(key2, "Value2");
        final String key3 = "Key3";
        map.put(key3, "Value3");

        // Check class invariants (precondition)
        assertClassInvariants(map);

        int oldSize = (int) getValueByFieldName(map, "size");
        int oldModCount = (int) getValueByFieldName(map, "modCount");

        // Check the assignable clause
        assertAssignableClauseForRemove(key1);

        // Assert postcondition
        assertThat(map.size(), is(2));
        assertThat((int) getValueByFieldName(map, "size"), is(oldSize - 1));
        assertThat((int) getValueByFieldName(map, "modCount"), not(is(oldModCount)));
        assertThat((String) invokeMethodWithParams(map, "remove", key2), is("Value2"));

        // Check class invariants (postcondition)
        assertClassInvariants(map);
    }

    /**
     * Tests the normal behaviour the method {@link IdentityHashMap#remove(Object)}
     * when the key to be removed does not exitst.
     * <p/>
     * JML to test:
     * <pre>
     *   assignable
     *     size, table, modCount;
     *   ensures
     *     size == \old(size) &&
     *     modCount == \old(modCount) &&
     *     \result == null;
     * </pre>
     *
     * @throws NoSuchFieldException   if one or more fields do not exist
     * @throws IllegalAccessException if one or more field cannot be accessed
     * @throws NoSuchMethodException  if the method to invoke does not exist
     * @throws NoSuchClassException   if one of the (inner) classes does not exist
     */
    @Test
    public void testRemoveNormalBehaviourWhenKeyDoesNotExist()
            throws NoSuchMethodException, IllegalAccessException,
            NoSuchFieldException, NoSuchClassException, InvocationTargetException {

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

        // Check the assignable clause
        assertAssignableClauseForRemove("unknownKey");

        // Assert postcondition
        assertThat(map.size(), is(3));
        assertThat((int) getValueByFieldName(map, "size"), is(oldSize));
        assertThat((int) getValueByFieldName(map, "modCount"), is(oldModCount));
        assertThat((String) invokeMethodWithParams(map, "remove", "unknownKey"), nullValue());

        // Check class invariants (post-condition)
        assertClassInvariants(map);
    }

    // Check assignable clause: assignable szie, table, modCount
    private void assertAssignableClauseForRemove(String key)
            throws NoSuchFieldException, IllegalAccessException,
            NoSuchMethodException {
        assertAssignableClause(
                map,
                "remove",
                new String[]{key},
                new String[]{"size", "table", "modCount"}
        );
    }

}
