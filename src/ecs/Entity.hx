package ecs;

#if macro
import haxe.macro.Expr;

using ecs.core.macro.ComponentBuilder;
using ecs.core.macro.ViewsOfComponentBuilder;
using ecs.core.macro.MacroTools;
using haxe.macro.Context;
using Lambda;
using tink.MacroApi;
using StringTools;

#end

/**
 * Entity is an abstract over the `Int` key.  
 * - Do not use the Entity as a unique id, as destroyed entities will be cached and reused!  
 *  
 * @author https://github.com/deepcake
 */
abstract Entity(Int) from Int to Int {
	public static inline var INVALID_ENTITY:Entity = Workflow.INVALID_ID;

	/**
	 * Creates a new Entity instance  
	 * @param immediate immediately adds this entity to the workflow if `true`, otherwise `activate()` call is required
	 */
	public inline function new(worlds:Int = 0xffffffff, immediate = true) {
		this = Workflow.id(immediate, worlds);
	}

	public inline function worlds() {
		return Workflow.worlds(this);
	}

	/**
	 * Adds this entity to the workflow, so it can be collected by views  
	 */
	public inline function activate() {
		Workflow.add(this);
	}

	/**
	 * Removes this entity from the workflow (and also from all views), but saves all associated components.  
	 * Entity can be added to the workflow again by `activate()` call
	 */
	public inline function deactivate() {
		Workflow.remove(this);
	}

	/**
	 * Prevents any addition callbaks until resuming
	 */
	public inline function pauseAdding() {
		Workflow.pauseAdding(this);
	}

	/**
	 * Calls any addition callbacks for new views
	 */
	public inline function resumeAdding() {
		Workflow.resumeAdding(this);
	}

	/**
	 * Returns the status of this entity: Active, Inactive, Cached or Invalid. Method is used mostly for debug purposes  
	 * @return Status
	 */
	public inline function status():Status {
		return Workflow.status(this);
	}

	/**
	 * Returns `true` if this entity is added to the workflow, otherwise returns `false`  
	 * @return Bool
	 */
	public inline function isActive():Bool {
		return Workflow.status(this) == Active;
	}

	/**
	 * Returns `true` if this entity has not been destroyed and therefore can be used safely  
	 * @return Bool
	 */
	public inline function isValid():Bool {
		return this != INVALID_ENTITY && Workflow.status(this) < Cached;
	}

	/**
	 * Removes all of associated to this entity components.  
	 * __Note__ that this entity will be still exists after call this method (just without any associated components). 
	 * If entity is not required anymore - `destroy()` should be called 
	 */
	public inline function removeAll() {
		Workflow.removeAllComponentsOf(this);
	}

	/**
	 * Removes this entity from the workflow with removing all associated components. 
	 * The `Int` id will be cached and then will be used again in new created entities.  
	 * __Note__ that using this entity after call this method is incorrect!
	 */
	public inline function destroy() {
		Workflow.cache(this);
	}

	/**
	 * Returns list of all associated to this entity components.  
	 * @return String
	 */
	public inline function print():String {
		return Workflow.printAllComponentsOf(this);
	}

	/**
	 * Adds a specified components to this entity.  
	 * If a component with the same type is already added - it will be replaced 
	 * @param components comma separated list of components of `Any` type
	 * @return `Entity`
	 */
	macro public function add(self:Expr, components:Array<Expr>):ExprOf<ecs.Entity> {
		var pos = Context.currentPos();

		if (components.length == 0) {
			Context.error('Required one or more Components', pos);
		}

		var addComponentsToContainersExprs = components.map(function(c) {
			var to = c.typeof();
			if (!to.isSuccess()) {
				Context.error('Can not find type for ${c} ', pos);
			}
			var info = switch (to.sure()) {
				case TType(tref, args):
					if (tref.get().name.contains("Class<")) {
						var cn = c.parseClassName();
						var clt = cn.getType();
						var tt = clt.follow();
						var compt = tt.toComplexType();
						compt.getComponentContainerInfo(pos);
					} else {
						// Typedef
						(to.sure().follow().toComplexType()).getComponentContainerInfo(pos);
					}
				// class is specified instead of an expression					
				default: 
					(to.sure().follow().toComplexType()).getComponentContainerInfo(pos);
			}

			return info.getAddExpr(macro __entity__, c);
			// var containerName = (c.typeof().follow().toComplexType()).getComponentContainerInfo().fullName;
			// return macro @:privateAccess $i{ containerName }.inst().add(__entity__, $c);
		});

		var body = [].concat(addComponentsToContainersExprs).concat([
			macro if (__entity__.isActive()) {
				for (v in ecs.Workflow.views) {
					@:privateAccess v.addIfMatched(__entity__);
				}
			}
		]).concat([macro return __entity__]);

		var ret = macro #if (haxe_ver >= 4) inline #end (function(__entity__:ecs.Entity) $b{body})($self);

		return ret;
	}

	/**
	 * Removes a component from this entity with specified type  
	 * @param types comma separated `Class<Any>` types of components that should be removed
	 * @return `Entity`
	 */
	macro public function remove(self:Expr, types:Array<ExprOf<Class<Any>>>):ExprOf<ecs.Entity> {
		var pos = Context.currentPos();
		var errorStage = "";
		if (types.length == 0) {
			Context.error('Required one or more Component Types', pos);
		}
		errorStage = "starting";
		var cts = types.map(function(type) {
			return type.parseClassName().getType().follow().toComplexType();
		});

		errorStage = "found types";
		var removeComponentsFromContainersExprs = cts.map(function(ct) {
			var info = ct.getComponentContainerInfo(pos);
			return info.getRemoveExpr(macro __entity__);
		});
		errorStage = "got remove expression";

		var removeEntityFromRelatedViewsExprs = cts.map(function(ct) {
			return ct.getViewsOfComponent(pos).followName(pos);
		}).map(function(viewsOfComponentClassName) {
			var x = viewsOfComponentClassName.asTypeIdent(Context.currentPos());
			return macro @:privateAccess $x.inst().removeIfMatched(__entity__);
		});
		errorStage = "got views of components";

		var body = [].concat([
			macro if (__entity__.isActive())
				$b{removeEntityFromRelatedViewsExprs}
		]).concat(removeComponentsFromContainersExprs).concat([macro return __entity__]);

		errorStage = "made body";

		var ret = macro inline(function(__entity__:ecs.Entity) $b{body})($self);

		errorStage = "returning";

		return ret;
	}

	#if bored_and_want_to_fix
	/**
	 * Returns a component of this entity of specified type.  
	 * If a component with specified type is not added to this entity, `null` will be returned 
	 * @param type `Class<T:Any>` type of component
	 * @return `T:Any` component instance
	 */
	macro public function getOrAdd<T>(self:Expr, type:ExprOf<Class<T>>):ExprOf<T> {
		var info = (type.parseClassName().getType().follow().toComplexType()).getComponentContainerInfo();
		var exists = info.getExistsExpr(self);
		var get = info.getGetExpr(self);

		return macro if ($exists) {
			return $get;
		} else {
			/*
				var addComponentsToContainersExprs = components.map(function(c) {
					var to = c.typeof();
					if (!to.isSuccess()) {
						Context.error('Can not find type for ${c}', Context.currentPos());
					}
					var info = (c.typeof().sure().follow().toComplexType()).getComponentContainerInfo();
					return info.getAddExpr(macro __entity__, c);
					// var containerName = (c.typeof().follow().toComplexType()).getComponentContainerInfo().fullName;
					// return macro @:privateAccess $i{ containerName }.inst().add(__entity__, $c);
				});

				var body = [].concat(addComponentsToContainersExprs).concat([
					macro if (__entity__.isActive()) {
						for (v in ecs.Workflow.views) {
							@:privateAccess v.addIfMatched(__entity__);
						}
					}
				]).concat([macro return __entity__]);

				var ret = macro #if (haxe_ver >= 4) inline #end (function(__entity__:ecs.Entity) $b{body})($self);

			 */
		};
	}
	#end

	/**
	 * Returns a component of this entity of specified type.  
	 * If a component with specified type is not added to this entity, `null` will be returned 
	 * @param type `Class<T:Any>` type of component
	 * @return `T:Any` component instance
	 */
	macro public function get<T>(self:Expr, type:ExprOf<Class<T>>):ExprOf<T> {
		var pos = Context.currentPos();
		var info = (type.parseClassName().getType().follow().toComplexType()).getComponentContainerInfo(pos);

		return info.getGetExpr(self);
	}

	/**
	 * Returns `true` if this entity contains a component of specified type, otherwise returns `false` 
	 * @param type `Class<T:Any>` type of component
	 * @return `Bool`
	 */
	macro public function exists(self:Expr, type:ExprOf<Class<Any>>):ExprOf<Bool> {
		var pos = Context.currentPos();
		var info = (type.parseClassName().getType().follow().toComplexType()).getComponentContainerInfo(pos);
		return info.getExistsExpr(self);
	}

	macro public function has(self:Expr, type:ExprOf<Class<Any>>):ExprOf<Bool> {
		var pos = Context.currentPos();
		var info = (type.parseClassName().getType().follow().toComplexType()).getComponentContainerInfo(pos);

		return info.getExistsExpr(self);
	}
}

@:enum abstract Status(Int) {
	var Inactive = 0;
	var Active = 1;
	var Cached = 2;
	var Invalid = 3;

	@:op(A > B) static function gt(a:Status, b:Status):Bool;

	@:op(A < B) static function lt(a:Status, b:Status):Bool;
}
