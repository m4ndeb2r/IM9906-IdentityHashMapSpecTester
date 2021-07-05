package nl.ou.im9906;

import org.junit.Test;

import java.lang.reflect.InvocationTargetException;
import java.util.IdentityHashMap;

import static nl.ou.im9906.MethodTestHelper.assertIsPureMethod;
import static nl.ou.im9906.ReflectionUtils.getValueByFieldName;
import static nl.ou.im9906.ReflectionUtils.invokeMethodWithParams;
import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.core.Is.is;

/**
 * Tests the JML specifications of the {@link IdentityHashMap#unmaskNull(Object)} ()} method.
 */
public class IdentityHashMapUnmaskNullTest {

    /**
     * Tests the purity of the method {@link IdentityHashMap#unmaskNull(Object)}, as
     * well as the following postcondition:
     * <pre>
     *    ensures
     *      key == NULL_KEY ==> \result == null &&
     *      key != NULL_KEY ==> \result == key;
     * </pre>
     *
     * @throws NoSuchFieldException      if one or more fields do not exist
     * @throws IllegalAccessException    if one or more field cannot be accessed
     * @throws NoSuchMethodException     if the method to invoke does not exist
     * @throws NoSuchClassException      if one of the (inner) classes does not exist
     * @throws InvocationTargetException if an exception occurs during the invocation of maskNull
     */
    @Test
    public void testUnmaskNullNormalBehaviour()
            throws NoSuchFieldException, IllegalAccessException,
            NoSuchMethodException, NoSuchClassException, InvocationTargetException {
        final IdentityHashMap<Object, Object> map = new IdentityHashMap<>();
        final Object null_key = getValueByFieldName(map, "NULL_KEY");

        assertThat((String)invokeMethodWithParams(map, "unmaskNull", "key"), is("key"));
        assertIsPureMethod(map, "unmaskNull", "key");

        assertThat(invokeMethodWithParams(map, "unmaskNull", null_key) == null, is(true));
        assertIsPureMethod(map, "unmaskNull", null_key);
    }
}
