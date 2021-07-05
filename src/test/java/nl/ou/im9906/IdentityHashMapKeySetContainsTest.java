package nl.ou.im9906;

import org.junit.Test;

import java.lang.reflect.InvocationTargetException;
import java.util.IdentityHashMap;

import static nl.ou.im9906.ClassInvariantTestHelper.assertClassInvariants;
import static nl.ou.im9906.MethodTestHelper.assertIsPureMethod;
import static nl.ou.im9906.ReflectionUtils.invokeMethodWithParams;
import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.core.Is.is;

/**
 * Tests the JML specifications of the {@link IdentityHashMap.KeySet#contains(Object)} method.
 *
 * Note: the contains method of the {@link IdentityHashMap.KeySet} is not verfified with KeY.
 * The JML may, therefore, still be incomplete or incorrect. So may this test.
 */
public class IdentityHashMapKeySetContainsTest {

    /**
     * Tests the normal behaviour of the method {@link IdentityHashMap.KeySet#size()}.
     * The size method is a pure method and has no side effects. This will be
     * tested by checking if none of the fields will be altered. There is no
     * precondition specified for the method, so only the class invariant should
     * hold as a precondition (and as a postcondition as well, obviously).
     * <p/>
     * JML specification to check:
     * <pre>
     *   public normal_behavior
     *     ensures \result == containsKey(o);
     * </pre>
     * Also tests the purity of the constructor, meaning (in terms of JML):
     * <pre>
     *   assignable \nothing;
     * </pre>
     *
     * @throws NoSuchFieldException      if one or more fields do not exist
     * @throws IllegalAccessException    if one or more field cannot be accessed
     * @throws NoSuchMethodException     if the method to invoke does not exist
     * @throws NoSuchClassException      if any of the expected inner classes does not exist
     * @throws InvocationTargetException if invocation of the contains method throws an exception
     */
    @Test
    public void testKeySetContainsNormalBehaviour()
            throws NoSuchFieldException, IllegalAccessException,
            NoSuchMethodException, NoSuchClassException,
            InvocationTargetException {
        final String key1 = "key1";
        final String key2 = "key2";
        final IdentityHashMap<Object, Object> map = new IdentityHashMap<>();
        map.put(key1, "value1");
        map.put(key2, "value2");

        // Test if the class invariants hold (precondition)
        assertClassInvariants(map);

        // Postcondition: \result == containsKey(o)
        assertThat((Boolean)invokeMethodWithParams(map.keySet(), "contains", key1), is(map.containsKey(key1)));
        assertThat((Boolean)invokeMethodWithParams(map.keySet(), "contains", key1), is(true));
        assertThat((Boolean)invokeMethodWithParams(map.keySet(), "contains", key2), is(map.containsKey(key2)));
        assertThat((Boolean)invokeMethodWithParams(map.keySet(), "contains", key2), is(true));
        assertThat((Boolean)invokeMethodWithParams(map.keySet(), "contains", "key3"), is(map.containsKey("key3")));
        assertThat((Boolean)invokeMethodWithParams(map.keySet(), "contains", "key3"), is(false));

        // Test if the class invariants hold (postcondition)
        assertClassInvariants(map);

        // Test if the size method is pure
        // TODO: this only tests the fields of the IdentityHashMap.KeySet class, not the
        //  fields of the IdentityHashMap class.
        assertIsPureMethod(map.keySet(), "contains", key1);
    }

}
