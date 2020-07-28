package nl.ou.im9906;

import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.ExpectedException;

import java.lang.reflect.InvocationTargetException;
import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.Map;

import static nl.ou.im9906.ClassInvariantTestHelper.assertClassInvariants;
import static nl.ou.im9906.ReflectionUtils.getValueByFieldName;
import static nl.ou.im9906.ReflectionUtils.invokeMethodWithParams;
import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.core.Is.is;

/**
 * Tests the JML specifications of the {@link IdentityHashMap}'s constructors.
 */
public class IdentityHashMapConstructorsTest {

    @Rule
    public ExpectedException expectedException = ExpectedException.none();

    /**
     * Tests the postcondition of the default constructor of the {@link IdentityHashMap}. The
     * length of the private field table is expected to be 2 * DEFAULT_CAPACITY = 64, and the
     * exptected size of the map is 0.
     * </p>
     * JML specification to check:
     * <pre>
     *   public normal_behavior
     *       ensures
     *           DEFAULT_CAPACITY == 32 &&
     *           table.length == (\bigint)2 * DEFAULT_CAPACITY &&
     *           size == 0;
     * </pre>
     * </p>
     * Obviously, the class invariants must hold after invoking the constructor. This is also
     * being checked.
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
     * Tests the postcondition of the constructor of the {@link IdentityHashMap} accepting a
     * preferred capacity for an argument. When a negative value is passed, an
     * IllegalArgumentException is expected.
     * </p>
     * JML specification to check:
     * <pre>
     *     public exceptional_behavior
     *       requires
     *         expectedMaxSize < 0;
     *       signals_only
     *         IllegalArgumentException;
     *       signals
     *         (IllegalArgumentException e) true;
     * </pre>
     */
    @Test
    public void testConstructorWithPreferredCapacityExceptionalBehavior() {
        expectedException.expect(IllegalArgumentException.class);
        new IdentityHashMap<>(-1);
    }

    /**
     * Tests the postcondition of the constructor of the {@link IdentityHashMap} accepting a
     * expected max size for an argument. When a non-negative value is passed, we expect the
     * length of the table array to be determined by the capacity method.
     * </p>
     * JML specification to check:
     * <pre>
     *     public normal_behavior
     *       requires
     *         expectedMaxSize >= 0;
     *       ensures
     *         table.length == (\bigint)2 * capacity(expectedMaxSize) &&
     *         size == 0;
     * </pre>
     * </p>
     * Obviously, the class invariants must hold after invoking the constructor. This is also
     * being checked.
     *
     * @throws NoSuchMethodException
     * @throws InvocationTargetException
     * @throws IllegalAccessException
     * @throws NoSuchFieldException
     * @throws InstantiationException
     * @throws NoSuchClassException
     */
    @Test
    public void testConstructorWithExpectedMaxSizeNormalBehavior()
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
     * Test the exceptional_behaviour of the constructor of {@link IdentityHashMap} when
     * {@code null} is passed as a parameter.
     * </p>
     * JML specification to check:
     * <pre>
     *     public exceptional_behavior
     *       requires
     *         m == null;
     *       signals_only
     *         NullPointerException;
     *       signals
     *         (NullPointerException e) true;
     * </pre>
     */
    @Test
    public void testConstructorWithMapArgumentExceptionalBehavior() {
        expectedException.expect(NullPointerException.class);
        new IdentityHashMap<>(null);
    }

    /**
     * Checks the postcondition of the constructor of {@link IdentityHashMap} accepting
     * a {@code Map} as an input parameter, in case normal_behavior.
     * </p>
     * JML specification to check:
     * <pre>
     *     public normal_behavior
     *       requires
     *         m != null;
     *       ensures
     *         size == m.size() &&
     *         (\forall \bigint i;
     *             0 <= i < table.length - 1 && i % 2 == 0;
     *             m.get(table[i]) == table[i+1]);
     * </pre>
     * </p>
     * Obviously, the class invariants must hold after invoking the constructor. This is also
     * checked.
     *
     * @throws InvocationTargetException
     * @throws NoSuchMethodException
     * @throws InstantiationException
     * @throws IllegalAccessException
     * @throws NoSuchFieldException
     * @throws NoSuchClassException
     */
    @Test
    public void testConstructorWithMapArgumentNormalBehavior()
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
