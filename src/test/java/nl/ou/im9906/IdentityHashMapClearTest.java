package nl.ou.im9906;

import org.junit.Before;
import org.junit.Test;

import java.util.IdentityHashMap;

import static nl.ou.im9906.ClassInvariantTestHelper.assertClassInvariants;
import static nl.ou.im9906.ReflectionUtils.getValueByFieldName;
import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.Matchers.not;
import static org.hamcrest.Matchers.nullValue;
import static org.hamcrest.core.Is.is;

/**
 * Tests the JML specifications of the {@link IdentityHashMap#clear()}
 * method.
 */
public class IdentityHashMapClearTest {

    private IdentityHashMap<Object, Object> map;

    @Before
    public void setUp() {
        map = new IdentityHashMap<>();

        final String key1 = "Key1";
        final String value1 = "Value1";

        final String key2 = "Key2";
        final String value2 = "Value2";

        final String key3 = "Key3";
        final String value3 = "Value3";

        map.put(key1, value1);
        map.put(key2, value2);
        map.put(key3, value3);
    }

    /**
     * Tests the normal behaviour the method {@link IdentityHashMap#clear()}
     * <p/>
     * JML:
     * <pre>
     *    assignable
     *      modCount, size, table;
     *    ensures
     *      \old(modCount) != modCount &&
     *      \old(table.length) == table.length &&
     *      size == 0 &&
     *      (\forall int i;
     *         0 <= i < table.length;
     *         table[i] == null);
     * </pre>
     *
     * throws NoSuchFieldException   if one or more fields do not exist
     * throws IllegalAccessException if one or more field cannot be accessed
     * throws NoSuchMethodException  if the method to invoke does not exist
     * throws NoSuchClassException   if one of the (inner) classes does not exist
     */
    @Test
    public void testClearNormalBehaviour()
            throws NoSuchMethodException, IllegalAccessException,
            NoSuchFieldException, NoSuchClassException {

        // Check class invariants (precondition)
        assertClassInvariants(map);

        final Object[] oldTable = (Object[]) getValueByFieldName(map, "table");
        final int oldLen = oldTable.length;
        final int oldModCount = (int) getValueByFieldName(map, "modCount");

        map.clear();

        final Object[] newTable = (Object[]) getValueByFieldName(map, "table");
        final int newLen = newTable.length;
        final int newModCount = (int) getValueByFieldName(map, "modCount");

        // Check postcondition
        assertThat(map.size(), is(0));
        assertThat(oldLen, is(newLen));
        assertThat(oldModCount, not(newModCount));
        for(int i = 0; i < newTable.length; i++) {
            assertThat(newTable[i], nullValue());
        }

        // Check class invariants (postcondition)
        assertClassInvariants(map);
    }

}
