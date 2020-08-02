package nl.ou.im9906;

import org.hamcrest.Matchers;
import org.junit.Before;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.ExpectedException;

import java.lang.reflect.InvocationTargetException;
import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.Map;

import static nl.ou.im9906.ClassInvariantTestHelper.assertClassInvariants;
import static nl.ou.im9906.MethodTestHelper.assertAssignableClause;
import static nl.ou.im9906.MethodTestHelper.assertAssignableNothingClause;

import static nl.ou.im9906.ReflectionUtils.getValueByFieldName;
import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.Matchers.not;
import static org.hamcrest.Matchers.nullValue;
import static org.hamcrest.core.Is.is;

/**
 * Tests the JML specifications of the {@link IdentityHashMap#put(Object, Object)}
 * method.
 */
public class IdentityHashMapPutTest {

    @Rule
    public ExpectedException expectedException = ExpectedException.none();

    private IdentityHashMap<Object, Object> map;
    private static final String KEY = "key";

    @Before
    public void setUp() {
        map = new IdentityHashMap<>();
        map.put(KEY, "aValue");
    }

    // TODO: test exceptional behaviour (IllegalStatException). Problem: memory issues...
    //  See {@link IdentityHashMapResizeTest}

    /**
     * Tests the normal bevhaviour of the {@link IdentityHashMap#put(Object, Object)}
     * method.
     * <p/>
     * Tests the followin JML speciication:
     * <pre>
     *   assignable
     *     size, table, threshold, modCount;
     *     ((\exists \bigint i;
     *         0 <= i < \old(table.length) - (\bigint)1 && i % 2 == 0;
     *         \old(table[i]) == key)
     *         ==> size == \old(size) && modCount == \old(modCount) &&
     *         (\forall \bigint j;
     *             0 <= j < \old(table.length) - (\bigint)1 && j % 2 == 0;
     *             \old(table[j]) == key ==> \result == \old(table[j + 1]))) &&
     *     (!(\exists \bigint i;
     *         0 <= i < \old(table.length) - (\bigint)1 && i % 2 == 0;
     *         \old(table[i]) == key)
     *         ==> (size == \old(size) + (\bigint)1) && modCount != \old(modCount) && \result == null) &&
     *     (\exists \bigint i;
     *         0 <= i < table.length - 1 && i % 2 == 0;
     *         table[i] == key && table[i + 1] == value);
     * </pre>
     * Also, the class invariants are tested as a pre- and postcondition.
     *
     * @throws NoSuchFieldException   if one or more fields do not exist
     * @throws IllegalAccessException if one or more field cannot be accessed
     * @throws NoSuchMethodException  if the method to invoke does not exist
     * @throws NoSuchClassException   if any of the expected inner classes does not exist
     */
    @Test
    public void testPutNormalBehaviour()
            throws IllegalAccessException, NoSuchClassException,
            NoSuchFieldException, NoSuchMethodException {
        // Test the class invariants (precondition)
        assertClassInvariants(map);

        // When key already exists ... overwrite old element
        final int oldSize = map.size();
        final int oldModCount = (int) getValueByFieldName(map, "modCount");
        final Object oldValue = map.get(KEY);
        assertThat(map.put(KEY, "newValue"), is(oldValue));
        assertThat(map.size(), is(oldSize));
        assertThat((int) getValueByFieldName(map, "modCount"), is(oldModCount));
        Object[] table = (Object[]) getValueByFieldName(map, "table");

        // Make sure the new element exists
        boolean found = false;
        for (int i = 0; i < table.length; i++) {
            if (KEY.equals(table[i])) {
                assertThat((String)table[i+1], is("newValue"));
                found = true;
            }
        }
        assertThat(found, is(true));

        // When key does not yet exists ... element should be added
        final String newKey = "newKey";
        assertThat(map.put(newKey, "otherNewValue"), nullValue());
        assertThat(map.size(), is(oldSize + 1));
        assertThat((int) getValueByFieldName(map, "modCount"), not(oldModCount));
        table = (Object[]) getValueByFieldName(map, "table");

        // Make sure the new element exists
        found = false;
        for (int i = 0; i < table.length; i++) {
            if (newKey.equals(table[i])) {
                assertThat((String)table[i+1], is("otherNewValue"));
                found = true;
            }
        }
        assertThat(found, is(true));

        // Test the assignability
        assertAssignableClause(map, "put", new String[]{"k", "v"}, new String[]{"size", "table", "threshold", "modCount"});

        // Test the class invariants (postcondition)
        assertClassInvariants(map);
    }

}
