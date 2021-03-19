package nl.ou.im9906;

import org.junit.Test;

import java.lang.reflect.InvocationTargetException;
import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.Map;

import static nl.ou.im9906.ClassInvariantTestHelper.assertClassInvariants;
import static nl.ou.im9906.ReflectionUtils.getValueByFieldName;
import static nl.ou.im9906.ReflectionUtils.invokeMethodWithParams;
import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.core.Is.is;
import static org.junit.Assert.fail;

/**
 * Tests the JML specifications of the {@link IdentityHashMap}'s constructors.
 */
public class IdentityHashMapConstructorsTest {

    /**
     * Tests the normal behaviour of the default constructor of the {@link IdentityHashMap}.
     * The length of the private field table is expected to be 2 * DEFAULT_CAPACITY = 64,
     * and the exptected size of the map is 0.
     * <p/>
     * JML specification to check:
     * <pre>
     *   ensures
     *     DEFAULT_CAPACITY == 32 &&
     *     table.length == 2 * DEFAULT_CAPACITY &&
     *     size == 0;
     * </pre>
     * <p/>
     * Obviously, the class invariants must hold after invoking the constructor. This is also
     * checked.
     *
     * @throws NoSuchFieldException   if the expected private field table does not exist
     * @throws IllegalAccessException if it was not possible to get acces to the private field
     * @throws NoSuchClassException   if any of the expected (inner) classes does not exist
     */
    @Test
    public void testDefaultConstructorPostCondition()
            throws NoSuchFieldException, IllegalAccessException, NoSuchClassException {
        // Call default constructor
        final IdentityHashMap<Object, Object> map = new IdentityHashMap<>();

        // Check the default capacity (length of field table, and value of field size)
        final int defaultCapacity = (int) getValueByFieldName(map, "DEFAULT_CAPACITY");
        assertThat(((Object[]) getValueByFieldName(map, "table")).length, is(2 * defaultCapacity));
        assertThat(map.size(), is(0));

        // After invoking the constructor, the class invariants must hold.
        assertClassInvariants(map);
    }

    /**
     * Tests the exceptional behaviour of the constructor of the {@link IdentityHashMap}
     * that accepts an expected max size for an argument. When a negative value is passed,
     * an IllegalArgumentException is expected.
     * <p/>
     * JML specification to check:
     * <pre>
     *   requires
     *     expectedMaxSize < 0;
     *   signals_only
     *     IllegalArgumentException;
     *   signals
     *     (IllegalArgumentException e) true;
     * </pre>
     */
    @Test
    public void testConstructorWithPreferredCapacityExceptionalBehaviour() {
        try {
            new IdentityHashMap<>(-1);
        } catch (IllegalArgumentException e) {
            return;
        }
        fail("Expected an IllegalArgumentException.");
    }

    /**
     * This test exposes an overflow error in the capacity method. When the capacity method is invoked
     * with an expectedMaxSize greater than MAXIMUM_CAPACITY, is should return a capacity of MAXIMUM_CAPACITY.
     * However, due to an overflow error in {@link IdentityHashMap#capacity(int)}, this is not always the case.
     * When we attempt to instantiate an {@link IdentityHashMap} with an expectedMaxSize 1431655768, for example,
     * we would expect it to contain a table array of 2 * MAXIMUM_CAPACITY elements. Instead, it only has 8 elements.
     *
     * @throws NoSuchFieldException
     * @throws IllegalAccessException
     */
    @Test
    public void testConstructorOverflowError() throws NoSuchFieldException, IllegalAccessException {
        final IdentityHashMap<Object, Object> map = new IdentityHashMap<>(1431655768);
        final int max = (int) getValueByFieldName(map, "MAXIMUM_CAPACITY");
        assertThat(((Object[]) getValueByFieldName(map, "table")).length, is(2 * max)); // FAILS because of overflow
    }

    /**
     * Tests the normal behaviour of the constructor of the {@link IdentityHashMap}
     * that accepts an expected max size for an argument. When a non-negative value
     * is passed, we expect the length of the table array to be determined by the
     * capacity method.
     * <p/>
     * JML specification to check:
     * <pre>
     *   requires
     *     expectedMaxSize >= 0;
     *   ensures
     *     table.length == 2 * capacity(expectedMaxSize) &&
     *     size == 0;
     * </pre>
     * <p/>
     * Obviously, the class invariants must hold after invoking the constructor. This is also
     * checked.
     *
     * @throws NoSuchMethodException
     * @throws InvocationTargetException
     * @throws IllegalAccessException
     * @throws NoSuchFieldException
     * @throws InstantiationException
     * @throws NoSuchClassException
     */
    @Test
    public void testConstructorWithExpectedMaxSizeNormalBehaviour()
            throws NoSuchMethodException, InvocationTargetException, IllegalAccessException, NoSuchFieldException, InstantiationException, NoSuchClassException {
        IdentityHashMap<String, String> map = new IdentityHashMap<>(0);
        int capacity = (int) invokeMethodWithParams(map, "capacity", 0);
        assertThat(((Object[]) getValueByFieldName(map, "table")).length, is(2 * capacity));
        assertThat(map.size(), is(0));

        final int largeInt = Integer.MAX_VALUE / 1024;
        map = new IdentityHashMap<>(largeInt);
        capacity = (int) invokeMethodWithParams(map, "capacity", largeInt);
        assertThat(((Object[]) getValueByFieldName(map, "table")).length, is(2 * capacity));
        assertThat(map.size(), is(0));

        // After invoking the constructor, the class invariants must hold.
        assertClassInvariants(map);
    }

    /**
     * Test the exceptional behaviour of the constructor of {@link IdentityHashMap} when
     * {@code null} is passed as a parameter.
     * <p/>
     * JML specification to check:
     * <pre>
     *   requires
     *     m == null;
     *   signals_only
     *     NullPointerException;
     *   signals
     *     (NullPointerException e) true;
     * </pre>
     */
    @Test
    public void testConstructorWithMapArgumentExceptionalBehaviour() {
        try {
            new IdentityHashMap<>(null);
        } catch (NullPointerException e) {
            return;
        }
        fail("Expected a NullPointerException.");
    }

    /**
     * Checks the norman behaviour of the constructor of {@link IdentityHashMap}
     * accepting a {@code Map} as an input parameter.
     * <p/>
     * JML specification to check:
     * <pre>
     *   requires
     *     m != null;
     *   ensures
     *     size == m.size() &&
     *     (\forall int i;
     *         0 <= i < table.length - 1;
     *         i % 2 == 0 ==> m.get(table[i]) == table[i+1]);
     * </pre>
     * <p/>
     * Obviously, the class invariants must hold after invoking the constructor. This
     * is also checked.
     *
     * @throws InvocationTargetException
     * @throws NoSuchMethodException
     * @throws InstantiationException
     * @throws IllegalAccessException
     * @throws NoSuchFieldException
     * @throws NoSuchClassException
     */
    @Test
    public void testConstructorWithMapArgumentNormalBehaviour()
            throws InvocationTargetException, NoSuchMethodException, InstantiationException,
            IllegalAccessException, NoSuchFieldException, NoSuchClassException {
        final Map<String, String> paramMap = new HashMap<>();
        paramMap.put("aKey", "aValue");
        paramMap.put("anotherKey", "anotherValue");

        final IdentityHashMap<String, String> map = new IdentityHashMap<>(paramMap);

        // Check the size and the table content
        assertThat(map.size(), is(paramMap.size()));
        final Object[] table = (Object[]) getValueByFieldName(map, "table");
        for (int i = 0; i < table.length; i += 2) {
            assertThat(paramMap.get(table[i]), is(table[i + 1]));
        }

        // After invoking the constructor, the class invariants must hold.
        assertClassInvariants(map);
    }

}
